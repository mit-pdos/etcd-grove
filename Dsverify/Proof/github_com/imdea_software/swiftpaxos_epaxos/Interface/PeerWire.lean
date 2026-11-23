/-
The wire format of the replicas' peer streams (`notes/stage1-plan.md`, "Connection roles"), pure:

* `uvarintEnc`, `varintEnc` (`binary.PutUvarint`, `binary.PutVarint`: little-endian base-128
  groups, the high bit a continuation flag; `PutVarint` zig-zags the `int64` first), and
  `encLen n` (`PutVarint(int64(n))` of a length `n`);
* one encoder per message, byte for byte as its `Marshal` writes it (`epaxos/defs.go`;
  `replica/defs/defs.go` for the beacons): the fixed-size header (`int32`s little-endian, then
  the `int8` statuses), then the slices, each as `encLen` of its length and its elements
  (commands as `state.Command.Marshal`, `encCommand`; `int32`s as 4 bytes little-endian). The
  headers follow the code's order, which is not always the record's (`Accept` puts `Seq` in the
  header; `PreAcceptReply` puts `Status` after `Seq`);
* `encMsg m`: the message's code byte, then its body (what `SendMsg` / `SendBeacon` /
  `ReplyBeacon` write: `WriteByte(code)`, then `Marshal`);
* `encId d`: the dialer's handshake (`binary.LittleEndian.PutUint32(bs, uint32(r.Id))`);
* `Msg.wf`: the message is encodable as the decoder reads it back (every command's value below
  `2 ^ 16` bytes, `Value.Marshal`'s `uint16` length; slices shorter than `2 ^ 62`);
* `Msg.isProto`: the protocol messages (not the beacons): the positions of a stream's
  `msgSent` facts count only these (`Epaxos/Interface/Net.lean`).

Also `Pos.Countable` instances for `WCmd` and `Msg` (the ghost state stores messages).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Msg
public import Perennial.Std.Countable

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

/-! ## Varints -/

/-- `binary.PutUvarint`'s bytes for `n` (`n < 2 ^ 64`): seven bits at a time, least significant
first, every byte but the last with its high bit set. -/
def uvarintEnc (n : Nat) : List w8 :=
  if h : n < 128 then [W8 n] else W8 (n % 128 + 128) :: uvarintEnc (n / 128)
termination_by n
decreasing_by omega

/-- The zig-zag image of an `int64` (`PutVarint`: `uint64(x) << 1`, complemented when `x < 0`). -/
def zigzag (x : w64) : Nat :=
  let z := sint.Z x
  (if 0 ≤ z then 2 * z else -2 * z - 1).toNat

/-- `binary.PutVarint`'s bytes for `x`. -/
def varintEnc (x : w64) : List w8 := uvarintEnc (zigzag x)

/-- `PutVarint(int64(n))` of a slice length `n` (`n < 2 ^ 63`): the zig-zag image of a
non-negative `n` is `2 n`. -/
def encLen (n : Nat) : List w8 := uvarintEnc (2 * n)

theorem encLen_varint (n : Nat) (hn : n < 2 ^ 63) : encLen n = varintEnc (W64 n) := by
  unfold encLen varintEnc zigzag
  congr 1
  have h1 : sint.Z (W64 (n : Int)) = n := by word
  simp only [h1]
  split <;> omega

/-! ## Slices -/

/-- A `[]state.Command` field: its length, then each command (`state.Command.Marshal`). -/
def encCmds (cs : List WCmd) : List w8 :=
  encLen cs.length ++ (cs.map encCommand).flatten

/-- A `[]int32` field: its length, then each element, 4 bytes little-endian. -/
def encDeps (ds : List w32) : List w8 :=
  encLen ds.length ++ (ds.map u32Le).flatten

/-! ## Decoding lemmas (proof helpers, not interface)

Prefix-code facts: each encoder, followed by anything, determines its argument and the rest. -/

/-- Two lists split at equal-length prefixes. -/
theorem append_prefix_of_length_eq {α : Type _} {u v x y : List α} (hl : u.length = v.length)
    (h : u ++ x = v ++ y) : u = v ∧ x = y :=
  List.append_inj h hl

theorem singleton_prefix {α : Type _} (a b : α) (x y : List α) (h : [a] ++ x = [b] ++ y) :
    a = b ∧ x = y := by
  simpa using h

/-- The concatenation of a prefix code's words, of equally many words, is a prefix code. -/
theorem flatten_map_prefix {α β : Type _} (P : α → Prop) (f : α → List β)
    (hf : ∀ a b, P a → P b → ∀ x y, f a ++ x = f b ++ y → a = b ∧ x = y)
    (xs ys : List α) (ha : ∀ a ∈ xs, P a) (hb : ∀ b ∈ ys, P b) (hlen : xs.length = ys.length)
    (x y : List β) (h : (xs.map f).flatten ++ x = (ys.map f).flatten ++ y) : xs = ys ∧ x = y := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simpa using h
    | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
      obtain ⟨rfl, h1⟩ := hf _ _ (ha a (by simp)) (hb b (by simp)) _ _ h
      obtain ⟨rfl, rfl⟩ := ih ys (fun c hc => ha c (by simp [hc])) (fun c hc => hb c (by simp [hc]))
        (by simpa using hlen) h1
      exact ⟨rfl, rfl⟩

theorem u32Le_prefix (a b : w32) (x y : List w8) (h : u32Le a ++ x = u32Le b ++ y) :
    a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := append_prefix_of_length_eq (by simp only [u32Le_length]) h
  exact ⟨u32Le_inj h1, h2⟩

theorem u64Le_prefix (a b : w64) (x y : List w8) (h : u64Le a ++ x = u64Le b ++ y) :
    a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := append_prefix_of_length_eq (by simp only [u64Le_length]) h
  exact ⟨u64Le_inj h1, h2⟩

/-- Every 4-byte list is a `u32Le`. -/
theorem u32Le_surj (l : List w8) (h : l.length = 4) : ∃ x, l = u32Le x :=
  ⟨leToU32 l, (leToU32_le l h).symm⟩

/-- Every 8-byte list is a `u64Le`. -/
theorem u64Le_surj (l : List w8) (h : l.length = 8) : ∃ x, l = u64Le x :=
  ⟨leToU64 l, (leToU64_le l h).symm⟩

theorem uvarintEnc_prefix (a b : Nat) (x y : List w8)
    (h : uvarintEnc a ++ x = uvarintEnc b ++ y) : a = b ∧ x = y := by
  induction a using Nat.strongRecOn generalizing b x y with
  | _ a ih =>
  rw [uvarintEnc.eq_1 a, uvarintEnc.eq_1 b] at h
  by_cases ha : a < 128 <;> by_cases hb : b < 128 <;> simp only [ha, hb, dite_true, dite_false,
    List.cons_append, List.nil_append, List.cons.injEq] at h
  · obtain ⟨h1, h2⟩ := h
    have : (W8 a).toNat = (W8 b).toNat := by rw [h1]
    simp only [W8, BitVec.toNat_ofInt] at this
    exact ⟨by omega, h2⟩
  · have : (W8 a).toNat = (W8 ((b : Int) % 128 + 128)).toNat := by rw [h.1]
    simp only [W8, BitVec.toNat_ofInt] at this
    omega
  · have : (W8 ((a : Int) % 128 + 128)).toNat = (W8 b).toNat := by rw [h.1]
    simp only [W8, BitVec.toNat_ofInt] at this
    omega
  · obtain ⟨h1, h2⟩ := h
    have : (W8 ((a : Int) % 128 + 128)).toNat = (W8 ((b : Int) % 128 + 128)).toNat := by rw [h1]
    simp only [W8, BitVec.toNat_ofInt] at this
    obtain ⟨e, rfl⟩ := ih (a / 128) (by omega) (b / 128) x y h2
    refine ⟨?_, rfl⟩
    omega

theorem zigzag_inj (a b : w64) (h : zigzag a = zigzag b) : a = b := by
  unfold zigzag at h
  have : sint.Z a = sint.Z b := by
    simp only at h
    split at h <;> split at h <;> omega
  exact BitVec.eq_of_toInt_eq this

theorem varintEnc_prefix (a b : w64) (x y : List w8)
    (h : varintEnc a ++ x = varintEnc b ++ y) : a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := uvarintEnc_prefix _ _ _ _ h
  exact ⟨zigzag_inj _ _ h1, h2⟩

theorem encLen_prefix (a b : Nat) (x y : List w8)
    (h : encLen a ++ x = encLen b ++ y) : a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := uvarintEnc_prefix _ _ _ _ h
  exact ⟨by omega, h2⟩

theorem encValue_prefix (v w : List w8) (hv : v.length < 2 ^ 16) (hw : w.length < 2 ^ 16)
    (x y : List w8) (h : encValue v ++ x = encValue w ++ y) : v = w ∧ x = y := by
  simp only [encValue, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := u32Le_prefix _ _ _ _ h
  have hl : v.length = w.length := by
    have := congrArg BitVec.toNat h1
    simp only [W32, BitVec.toNat_ofInt] at this
    omega
  exact append_prefix_of_length_eq hl h2

theorem encDeps_prefix (ds es : List w32) (x y : List w8)
    (h : encDeps ds ++ x = encDeps es ++ y) : ds = es ∧ x = y := by
  simp only [encDeps, List.append_assoc] at h
  obtain ⟨hl, h⟩ := encLen_prefix _ _ _ _ h
  exact flatten_map_prefix (fun _ => True) u32Le (fun a b _ _ => u32Le_prefix a b)
    ds es (by simp) (by simp) hl x y h

namespace model

/-! ## The messages' bodies (`Marshal`) -/

def encPrepare (m : Prepare) : List w8 :=
  u32Le m.leaderId ++ u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot

def encPrepareReply (m : PrepareReply) : List w8 :=
  u32Le m.acceptorId ++ u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot ++ u32Le m.vballot ++
    [m.status] ++ encCmds m.command ++ u32Le m.seq ++ encDeps m.deps

def encPreAccept (m : PreAccept) : List w8 :=
  u32Le m.leaderId ++ u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot ++
    encCmds m.command ++ u32Le m.seq ++ encDeps m.deps

def encPreAcceptReply (m : PreAcceptReply) : List w8 :=
  u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot ++ u32Le m.vballot ++ u32Le m.seq ++
    [m.status] ++ encDeps m.deps ++ encDeps m.committedDeps

/-- `Accept.Marshal`: `Seq` is in the 20-byte header. -/
def encAccept (m : Accept) : List w8 :=
  u32Le m.leaderId ++ u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot ++ u32Le m.seq ++
    encCmds m.command ++ encDeps m.deps

def encAcceptReply (m : AcceptReply) : List w8 :=
  u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot

def encCommit (m : Commit) : List w8 :=
  u32Le m.leaderId ++ u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot ++
    encCmds m.command ++ u32Le m.seq ++ encDeps m.deps

def encTryPreAccept (m : TryPreAccept) : List w8 :=
  u32Le m.leaderId ++ u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot ++
    encCmds m.command ++ u32Le m.seq ++ encDeps m.deps

def encTryPreAcceptReply (m : TryPreAcceptReply) : List w8 :=
  u32Le m.acceptorId ++ u32Le m.replica ++ u32Le m.inst ++ u32Le m.ballot ++ u32Le m.vballot ++
    u32Le m.conflictReplica ++ u32Le m.conflictInstance ++ [m.conflictStatus]

/-- `defs.Beacon.Marshal` / `defs.BeaconReply.Marshal`: the timestamp, 8 bytes little-endian. -/
def encBeacon (ts : w64) : List w8 := u64Le ts

/-- A message's body, as its type's `Marshal` writes it. -/
def Msg.body : Msg → List w8
  | .prepare m => encPrepare m
  | .prepareReply m => encPrepareReply m
  | .preAccept m => encPreAccept m
  | .preAcceptReply m => encPreAcceptReply m
  | .accept m => encAccept m
  | .acceptReply m => encAcceptReply m
  | .commit m => encCommit m
  | .tryPreAccept m => encTryPreAccept m
  | .tryPreAcceptReply m => encTryPreAcceptReply m
  | .beacon ts => encBeacon ts
  | .beaconReply ts => encBeacon ts

/-- A message on a peer stream: its code byte, then its body. -/
def encMsg (m : Msg) : List w8 := [m.code] ++ m.body

/-- The protocol messages (not the framework's beacons). -/
def Msg.isProto : Msg → Bool
  | .beacon _ | .beaconReply _ => false
  | _ => true

/-- The protocol messages of a stream, in order (their positions are `msgSent`'s). -/
def protoMsgs (ws : List Msg) : List Msg := ws.filter Msg.isProto

/-! ## Well-formedness -/

/-- A command is encodable: its value is shorter than `2 ^ 16` bytes (`Value.Marshal` writes a
`uint16` length). -/
def cmdWf (c : WCmd) : Prop := c.val.length < 2 ^ 16

def cmdsWf (cs : List WCmd) : Prop := cs.length < 2 ^ 62 ∧ ∀ c ∈ cs, cmdWf c

def depsWf (ds : List w32) : Prop := ds.length < 2 ^ 62

/-- A message is encodable: its commands and slices are (`Unmarshal` reads back what `Marshal`
wrote). -/
def Msg.wf : Msg → Prop
  | .prepareReply m => cmdsWf m.command ∧ depsWf m.deps
  | .preAccept m => cmdsWf m.command ∧ depsWf m.deps
  | .preAcceptReply m => depsWf m.deps ∧ depsWf m.committedDeps
  | .accept m => cmdsWf m.command ∧ depsWf m.deps
  | .commit m => cmdsWf m.command ∧ depsWf m.deps
  | .tryPreAccept m => cmdsWf m.command ∧ depsWf m.deps
  | _ => True

/-! ## Decoding lemmas (proof helpers, not interface): commands and messages -/

theorem encCommand_prefix (a b : WCmd) (ha : cmdWf a) (hb : cmdWf b) (x y : List w8)
    (h : encCommand a ++ x = encCommand b ++ y) : a = b ∧ x = y := by
  obtain ⟨op, key, val⟩ := a
  obtain ⟨op', key', val'⟩ := b
  simp only [encCommand, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := singleton_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u64Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := encValue_prefix _ _ ha hb _ _ h2
  exact ⟨rfl, h3⟩

theorem encCmds_prefix (cs ds : List WCmd) (hc : ∀ c ∈ cs, cmdWf c)
    (hd : ∀ d ∈ ds, cmdWf d) (x y : List w8) (h : encCmds cs ++ x = encCmds ds ++ y) :
    cs = ds ∧ x = y := by
  simp only [encCmds, List.append_assoc] at h
  obtain ⟨hl, h⟩ := encLen_prefix _ _ _ _ h
  exact flatten_map_prefix cmdWf encCommand encCommand_prefix cs ds hc hd hl x y h

theorem encPrepare_prefix (a b : Prepare) (x y : List w8)
    (h : encPrepare a ++ x = encPrepare b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encPrepare, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  exact ⟨rfl, h4⟩

theorem encPrepareReply_prefix (a b : PrepareReply) (ha : cmdsWf a.command) (hb : cmdsWf b.command) (x y : List w8)
    (h : encPrepareReply a ++ x = encPrepareReply b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encPrepareReply, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := u32Le_prefix _ _ _ _ h4
  obtain ⟨rfl, h6⟩ := singleton_prefix _ _ _ _ h5
  obtain ⟨rfl, h7⟩ := encCmds_prefix _ _ ha.2 hb.2 _ _ h6
  obtain ⟨rfl, h8⟩ := u32Le_prefix _ _ _ _ h7
  obtain ⟨rfl, h9⟩ := encDeps_prefix _ _ _ _ h8
  exact ⟨rfl, h9⟩

theorem encPreAccept_prefix (a b : PreAccept) (ha : cmdsWf a.command) (hb : cmdsWf b.command) (x y : List w8)
    (h : encPreAccept a ++ x = encPreAccept b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encPreAccept, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := encCmds_prefix _ _ ha.2 hb.2 _ _ h4
  obtain ⟨rfl, h6⟩ := u32Le_prefix _ _ _ _ h5
  obtain ⟨rfl, h7⟩ := encDeps_prefix _ _ _ _ h6
  exact ⟨rfl, h7⟩

theorem encPreAcceptReply_prefix (a b : PreAcceptReply) (x y : List w8)
    (h : encPreAcceptReply a ++ x = encPreAcceptReply b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encPreAcceptReply, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := u32Le_prefix _ _ _ _ h4
  obtain ⟨rfl, h6⟩ := singleton_prefix _ _ _ _ h5
  obtain ⟨rfl, h7⟩ := encDeps_prefix _ _ _ _ h6
  obtain ⟨rfl, h8⟩ := encDeps_prefix _ _ _ _ h7
  exact ⟨rfl, h8⟩

theorem encAccept_prefix (a b : Accept) (ha : cmdsWf a.command) (hb : cmdsWf b.command) (x y : List w8)
    (h : encAccept a ++ x = encAccept b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encAccept, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := u32Le_prefix _ _ _ _ h4
  obtain ⟨rfl, h6⟩ := encCmds_prefix _ _ ha.2 hb.2 _ _ h5
  obtain ⟨rfl, h7⟩ := encDeps_prefix _ _ _ _ h6
  exact ⟨rfl, h7⟩

theorem encAcceptReply_prefix (a b : AcceptReply) (x y : List w8)
    (h : encAcceptReply a ++ x = encAcceptReply b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encAcceptReply, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  exact ⟨rfl, h3⟩

theorem encCommit_prefix (a b : Commit) (ha : cmdsWf a.command) (hb : cmdsWf b.command) (x y : List w8)
    (h : encCommit a ++ x = encCommit b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encCommit, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := encCmds_prefix _ _ ha.2 hb.2 _ _ h4
  obtain ⟨rfl, h6⟩ := u32Le_prefix _ _ _ _ h5
  obtain ⟨rfl, h7⟩ := encDeps_prefix _ _ _ _ h6
  exact ⟨rfl, h7⟩

theorem encTryPreAccept_prefix (a b : TryPreAccept) (ha : cmdsWf a.command) (hb : cmdsWf b.command) (x y : List w8)
    (h : encTryPreAccept a ++ x = encTryPreAccept b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encTryPreAccept, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := encCmds_prefix _ _ ha.2 hb.2 _ _ h4
  obtain ⟨rfl, h6⟩ := u32Le_prefix _ _ _ _ h5
  obtain ⟨rfl, h7⟩ := encDeps_prefix _ _ _ _ h6
  exact ⟨rfl, h7⟩

theorem encTryPreAcceptReply_prefix (a b : TryPreAcceptReply) (x y : List w8)
    (h : encTryPreAcceptReply a ++ x = encTryPreAcceptReply b ++ y) : a = b ∧ x = y := by
  cases a; cases b
  simp only [encTryPreAcceptReply, List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := u32Le_prefix _ _ _ _ h
  obtain ⟨rfl, h2⟩ := u32Le_prefix _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := u32Le_prefix _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := u32Le_prefix _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := u32Le_prefix _ _ _ _ h4
  obtain ⟨rfl, h6⟩ := u32Le_prefix _ _ _ _ h5
  obtain ⟨rfl, h7⟩ := u32Le_prefix _ _ _ _ h6
  obtain ⟨rfl, h8⟩ := singleton_prefix _ _ _ _ h7
  exact ⟨rfl, h8⟩

theorem encBeacon_prefix (a b : w64) (x y : List w8)
    (h : encBeacon a ++ x = encBeacon b ++ y) : a = b ∧ x = y :=
  u64Le_prefix a b x y h

/-- Two well-formed messages with the same code: their bodies (each followed by anything)
determine them. -/
theorem Msg.body_prefix (m m' : Msg) (hk : m.code = m'.code) (hwf : m.wf) (hwf' : m'.wf)
    (x y : List w8) (h : m.body ++ x = m'.body ++ y) : m = m' ∧ x = y := by
  have hk' := congrArg BitVec.toNat hk
  cases m <;> cases m' <;> simp only [Msg.code, BitVec.toNat_ofInt] at hk' <;>
    (try (exfalso; omega)) <;> simp only [Msg.body, Msg.wf] at h hwf hwf'
  · obtain ⟨rfl, h1⟩ := encPrepare_prefix _ _ _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encPrepareReply_prefix _ _ hwf.1 hwf'.1 _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encPreAccept_prefix _ _ hwf.1 hwf'.1 _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encPreAcceptReply_prefix _ _ _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encAccept_prefix _ _ hwf.1 hwf'.1 _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encAcceptReply_prefix _ _ _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encCommit_prefix _ _ hwf.1 hwf'.1 _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encTryPreAccept_prefix _ _ hwf.1 hwf'.1 _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encTryPreAcceptReply_prefix _ _ _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encBeacon_prefix _ _ _ _ h; exact ⟨rfl, h1⟩
  · obtain ⟨rfl, h1⟩ := encBeacon_prefix _ _ _ _ h; exact ⟨rfl, h1⟩

/-- `encMsg` is a prefix code on well-formed messages. -/
theorem encMsg_prefix (m m' : Msg) (hwf : m.wf) (hwf' : m'.wf) (x y : List w8)
    (h : encMsg m ++ x = encMsg m' ++ y) : m = m' ∧ x = y := by
  simp only [encMsg, List.append_assoc] at h
  obtain ⟨hk, h1⟩ := singleton_prefix _ _ _ _ h
  exact Msg.body_prefix m m' hk hwf hwf' x y h1

/-- A stream of whole messages determines them, in the reader's form: `encMsg` is injective on
well-formed messages, and no encoding is a proper prefix of another's (the decoder reads each
back exactly), so two decodings of the same bytes (each followed by anything) are in prefix
order. -/
theorem encMsg_prefix_inj (ms ms' : List Msg) (rest rest' : List w8)
    (hwf : ∀ m ∈ ms, m.wf) (hwf' : ∀ m ∈ ms', m.wf)
    (h : (ms.flatMap encMsg) ++ rest = (ms'.flatMap encMsg) ++ rest') : ms <+: ms' ∨ ms' <+: ms := by
  induction ms generalizing ms' with
  | nil => exact Or.inl (List.nil_prefix)
  | cons m ms ih =>
    cases ms' with
    | nil => exact Or.inr (List.nil_prefix)
    | cons m' ms' =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨rfl, h1⟩ := encMsg_prefix m m' (hwf m (by simp)) (hwf' m' (by simp)) _ _ h
      rcases ih ms' (fun c hc => hwf c (by simp [hc])) (fun c hc => hwf' c (by simp [hc])) h1
        with hp | hp
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)

/-- The equal-length form. -/
theorem encMsg_prefix_inj_len (ms ms' : List Msg) (rest rest' : List w8)
    (hwf : ∀ m ∈ ms, m.wf) (hwf' : ∀ m ∈ ms', m.wf) (hlen : ms.length = ms'.length)
    (h : (ms.flatMap encMsg) ++ rest = (ms'.flatMap encMsg) ++ rest') : ms = ms' := by
  rcases encMsg_prefix_inj ms ms' rest rest' hwf hwf' h with hp | hp
  · exact hp.eq_of_length hlen
  · exact (hp.eq_of_length hlen.symm).symm

end model

/-! ## The handshake -/

/-- The dialer's handshake on a peer connection: its replica id `d`, 4 bytes little-endian. -/
def encId (d : Nat) : List w8 := u32Le (W32 d)

/-! ## Countable instances (for the ghost state) -/

def WCmd.tup (c : WCmd) : w8 × w64 × List w8 := (c.op, c.key, c.val)

instance wcmd_countable : Pos.Countable WCmd :=
  .ofInjective (fun c => Pos.Countable.encode c.tup) (by
    intro a b h
    have h' := Pos.encode_inj h
    cases a; cases b; simp_all [WCmd.tup])

namespace model

/-- A message as a tuple (its code, its `int32`s, its `int8`s, its commands, its `[]int32`s, its
timestamp). -/
def Msg.tup : Msg → w8 × List w32 × List w8 × List WCmd × List (List w32) × w64
  | .prepare m => (W8 9, [m.leaderId, m.replica, m.inst, m.ballot], [], [], [], W64 0)
  | .prepareReply m => (W8 10, [m.acceptorId, m.replica, m.inst, m.ballot, m.vballot, m.seq],
      [m.status], m.command, [m.deps], W64 0)
  | .preAccept m => (W8 11, [m.leaderId, m.replica, m.inst, m.ballot, m.seq], [], m.command,
      [m.deps], W64 0)
  | .preAcceptReply m => (W8 12, [m.replica, m.inst, m.ballot, m.vballot, m.seq], [m.status],
      [], [m.deps, m.committedDeps], W64 0)
  | .accept m => (W8 13, [m.leaderId, m.replica, m.inst, m.ballot, m.seq], [], m.command,
      [m.deps], W64 0)
  | .acceptReply m => (W8 14, [m.replica, m.inst, m.ballot], [], [], [], W64 0)
  | .commit m => (W8 15, [m.leaderId, m.replica, m.inst, m.ballot, m.seq], [], m.command,
      [m.deps], W64 0)
  | .tryPreAccept m => (W8 16, [m.leaderId, m.replica, m.inst, m.ballot, m.seq], [], m.command,
      [m.deps], W64 0)
  | .tryPreAcceptReply m => (W8 17, [m.acceptorId, m.replica, m.inst, m.ballot, m.vballot,
      m.conflictReplica, m.conflictInstance], [m.conflictStatus], [], [], W64 0)
  | .beacon ts => (W8 6, [], [], [], [], ts)
  | .beaconReply ts => (W8 7, [], [], [], [], ts)

theorem Msg.tup_inj (a b : Msg) (h : a.tup = b.tup) : a = b := by
  cases a <;> cases b <;> simp [Msg.tup] at h <;>
    first
    | (exact absurd h.1 (by decide))
    | (exact absurd h (by decide))
    | (rename_i x y; cases x; cases y; simp_all)
    | simp_all

instance msg_countable : Pos.Countable Msg :=
  .ofInjective (fun m => Pos.Countable.encode m.tup) (fun a b h => Msg.tup_inj a b (Pos.encode_inj h))

end model

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
