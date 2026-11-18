/-
Iris reasoning principles for the TCP extension `netConnExt` (`Impl.lean`): its ghost state,
the interpretation of its state, its start resources, and specs of its operations (M2b,
`notes/harness-m2a.md`, "M2b result"). Not trusted: everything here is proved from `Impl.lean`.

**Ghost state.** Per connection `cid` and direction (a stream, named by the end that writes it,
`false` the dialer's, `true` the acceptor's), after Perennial's SPSC channel idiom:
* the writer owns half of a mono-list of every byte it has written (`sendTok cid side P W`), the
  state interpretation the other half;
* the reader owns half of a ghost variable holding every byte it has read (`recvTok cid side P
  R`), the state interpretation the other half, which keeps `R` a prefix of `W`;
* the bytes in the stream are `W` without `R` (the stream is live or `fin`) or a prefix of that
  (the stream is `cut`: a break lost a suffix, and later writes are thrown away);
* each direction has a protocol `P : w64 → List w8 → IProp` (a saved predicate), fixed per
  address: a writer appends `bs` only with `□ P cid (W ++ bs)`, and a reader learns `□ P cid ext`
  for some extension `ext` of what it has read (`protoPrefix`). So `P` says what the bytes mean
  (for a framing proof: "`ext` is the encoding of messages that satisfy Φ"); it may mention the
  other direction through `sentLb`.
A short write (one with any error: a timeout, the end closed meanwhile, a break) appends a
prefix of the buffer to `W` (`P` holds of an extension of it); a break or a timeout changes no
other ghost state: a reader's error result leaves `R` as it was, a writer's `W` grows by what the
write reports, whether or not the bytes survive.

**Listeners and addresses.** The configured addresses (`NetState.addrs`) each have, from the
start (`globalStart`), an address token (`addrTok a`, consumed by `Listen`, given back by the
listener's `Close`) and an unset protocol (`addrUnset a`, set once by the client to the
address's two predicates: `addrProto a P Q`, persistent). `Dial a` needs `addrProto a P Q` and
gives the dialer's end (`sendTok cid false P []`, `recvTok cid false Q []`); the acceptor's end
waits at the listener in the state interpretation until an `Accept` hands it over
(`sendTok cid true Q []`, `recvTok cid true P []`). A `Dial` that fails may also leave a
connection there (`Conn.abandoned`); its dialer's end is dropped, and its streams are empty, so
the acceptor's end of it is the same resource.

**Fresh ends.** `Dial` and `Accept` also hand out, once per connection and end, an exclusive
token `connFresh cid side` (`connFresh_excl`): the end is new. A client keying ghost state by
connection id uses it to do something exactly once per end: a dialer registering the
connection's ghost names in a global map keyed by `cid`, an acceptor claiming a role on the
connection. The tokens are elements of two ghost maps (one per side) whose authorities the state
interpretation keeps, with no key outside the connections named so far, so a new `cid` has
neither; `Dial` makes both, and keeps the acceptor's with the pending connection.

**Errors.** `Close` and the deadline setters need only `isConnP cid`: they change no ghost
state (a closed end's later operations fail without effect; `fin` and `live` streams have the
same invariant). `EOF`, a timeout, a break and "closed" are all just error results: the specs
do not distinguish them (a protocol cannot rely on `io.EOF`, which may follow a break).

**Why Hoare triples**, not `atomic_wp`: every resource an operation changes is owned by the
caller (the writer's mono-list half, the reader's ghost-variable half) or is persistent; what is
shared lives in the state interpretation. A connection used by two goroutines (a reader and a
writer) splits into `sendTok` and `recvTok`; one closing it from a third needs only `isConnP`.
A protocol needing a write under a lock puts `sendTok` in the lock's invariant. Nothing here
needs to open an invariant at a linearization point.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Golang.Defn.PostLang
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.Token
public import Harness.GooseLang.Ext.NetConn.Impl

@[expose] public section

noncomputable section

namespace Perennial

namespace NetConn

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost names -/

/-- The ghost names of a stream: the writer's mono-list of bytes written, the reader's ghost
variable of bytes read, the protocol (a saved predicate). -/
abbrev StreamNames := GName × GName × GName

/-- The ghost names of a connection: its streams `false` (written by the dialer) and `true`. -/
abbrev ConnNames := StreamNames × StreamNames

/-- The names of stream `s`. -/
def ConnNames.get (n : ConnNames) (s : Side) : StreamNames := if s then n.2 else n.1

@[simp] theorem ConnNames.get_false (n : ConnNames) : n.get false = n.1 := rfl
@[simp] theorem ConnNames.get_true (n : ConnNames) : n.get true = n.2 := rfl

/-- The ghost names of an address: its token, the protocols of the dialer's stream and of the
acceptor's stream. -/
abbrev AddrNames := GName × GName × GName

/-- A protocol: what the bytes of a stream of connection `cid` mean, as a predicate on the
whole sequence written (`□ P cid W` is required of every prefix the writer creates, up to
extension: `protoPrefix`). -/
abbrev Proto (GF : BundledGFunctors) := w64 → List w8 → IProp GF

/-! ## The streams' invariant, purely -/

/-- Stream `st` holds what was written (`W`) and not read (`R`, a prefix of `W`): exactly, while
the stream is live; a prefix of it otherwise (a break lost a suffix; after a `Close` nothing more
is appended). -/
def StreamRel (st : Stream) (W R : List w8) : Prop :=
  R <+: W ∧ (if st.status = .live then st.bytes = W.drop R.length else st.bytes <+: W.drop R.length)

theorem prefix_drop {a b : List w8} (h : a <+: b) (n : Nat) : a.drop n <+: b.drop n := by
  obtain ⟨t, rfl⟩ := h
  rw [List.drop_append]
  exact List.prefix_append _ _

theorem StreamRel.prefix {st : Stream} {W R : List w8} (h : StreamRel st W R) :
    st.bytes <+: W.drop R.length := by
  obtain ⟨_, h⟩ := h
  split at h
  · rw [h]; exact List.prefix_refl _
  · exact h

theorem StreamRel.cut {st st' : Stream} {W R : List w8} (h : StreamRel st W R)
    (hs : st'.status = .cut) (hb : st'.bytes <+: st.bytes) : StreamRel st' W R :=
  ⟨h.1, by rw [hs]; exact hb.trans h.prefix⟩

theorem StreamRel.close {st : Stream} {W R : List w8} (h : StreamRel st W R) :
    StreamRel (if st.status = .live then { st with status := .fin } else st) W R := by
  split
  · exact ⟨h.1, by simp only [reduceCtorEq, ite_false]; exact h.prefix⟩
  · exact h

theorem StreamRel.write {st : Stream} {W R : List w8} (h : StreamRel st W R) (d : List w8) :
    StreamRel (if st.status = .live then { st with bytes := st.bytes ++ d } else st)
      (W ++ d) R := by
  obtain ⟨hR, hb⟩ := h
  have hRW : R.length ≤ W.length := hR.length_le
  refine ⟨hR.trans (List.prefix_append _ _), ?_⟩
  split
  · rename_i hl
    simp only [hl, ite_true] at hb ⊢
    rw [hb, List.drop_append_of_le_length hRW]
  · rename_i hl
    simp only [hl, ite_false] at hb ⊢
    exact hb.trans (by rw [List.drop_append_of_le_length hRW]; exact List.prefix_append _ _)

theorem StreamRel.read {st : Stream} {W R data : List w8} (h : StreamRel st W R)
    (hd : data <+: st.bytes) :
    StreamRel { st with bytes := st.bytes.drop data.length } W (R ++ data) := by
  have hp := h.prefix
  have hRd : R ++ data <+: W := by
    obtain ⟨t, ht⟩ := hd.trans hp
    obtain ⟨u, hu⟩ := h.1
    refine ⟨t, ?_⟩
    rw [List.append_assoc, ht, ← hu, List.drop_left]
  refine ⟨hRd, ?_⟩
  obtain ⟨_, hb⟩ := h
  simp only [List.length_append]
  split
  · rename_i hl
    simp only [hl, ite_true] at hb
    rw [hb, List.drop_drop, Nat.add_comm]
  · rename_i hl
    simp only [hl, ite_false] at hb
    have := prefix_drop hb data.length
    rwa [List.drop_drop] at this


/-! ## The operations' outcomes and the invariant, purely -/

theorem Conn.setStream_stream (c : Conn) (s : Side) (st : Stream) (s' : Side) :
    (c.setStream s st).stream s' = if s' = s then st else c.stream s' := rfl

theorem Conn.setEnd_stream (c : Conn) (s : Side) (e : EndState) :
    (c.setEnd s e).stream = c.stream := rfl

theorem breakOrNot_rel {c c₁ : Conn} (h : BreakOrNot c c₁) :
    ∀ s W R, StreamRel (c.stream s) W R → StreamRel (c₁.stream s) W R := by
  rcases h with rfl | ⟨_, hb⟩
  · exact fun _ _ _ h => h
  · intro s W R hr
    exact hr.cut (hb s).1 (hb s).2

theorem close_rel {c c₂ : Conn} {side : Side} {code : w64} (h : CloseOutcome c side code c₂) :
    ∀ s W R, StreamRel (c.stream s) W R → StreamRel (c₂.stream s) W R := by
  unfold CloseOutcome at h
  dsimp only at h
  split at h
  · obtain ⟨_, rfl⟩ := h
    exact fun _ _ _ h => h
  · obtain ⟨_, rfl⟩ := h
    intro s W R hr
    rw [Conn.setStream_stream, Conn.setEnd_stream]
    split
    · subst s; exact hr.close
    · exact hr

theorem deadline_stream {c c₂ : Conn} {side : Side} {which : w64} {set : Bool} {code : w64}
    (h : DeadlineOutcome c side which set code c₂) : c₂.stream = c.stream := by
  unfold DeadlineOutcome at h
  dsimp only at h
  split at h
  · rw [h.2]
  · obtain ⟨_, h⟩ := h
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- A `Write`'s append (`WriteOutcome`'s `c₁`): the bytes `d` go on stream `side` if it is
live, and are discarded otherwise. -/
def Conn.writeAppend (c : Conn) (side : Side) (d : List w8) : Conn :=
  if (c.stream side).status = .live then
    c.setStream side { c.stream side with bytes := (c.stream side).bytes ++ d }
  else c

/-- `WriteOutcome`, with its append named. -/
theorem writeOutcome_iff (c : Conn) (side : Side) (data : List w8) (k : Nat) (code : w64)
    (c₂ : Conn) :
    WriteOutcome c side data k code c₂ ↔
      if (c.ends side).closed then k = 0 ∧ code = errClosed ∧ c₂ = c
      else k ≤ data.length ∧
        ((code = errNone ∧ k = data.length ∧ c₂ = c.writeAppend side (data.take k)) ∨
         (code = errTimeout ∧ (c.ends side).writeDeadline ∧
           c₂ = c.writeAppend side (data.take k)) ∨
         (code = errClosed ∧ c₂ = c.writeAppend side (data.take k)) ∨
         (code = errBroken ∧ (c.writeAppend side (data.take k)).Breaks c₂)) := Iff.rfl

theorem writeAppend_rel (c : Conn) (side : Side) (d : List w8) :
    (∀ W R, StreamRel (c.stream side) W R →
      StreamRel ((c.writeAppend side d).stream side) (W ++ d) R) ∧
    (c.writeAppend side d).stream (!side) = c.stream (!side) := by
  unfold Conn.writeAppend
  refine ⟨fun W R hr => ?_, ?_⟩
  · have := hr.write d
    split
    · rename_i hl
      simp only [hl, ite_true] at this
      rw [Conn.setStream_stream]; simp only [ite_true]; rw [hl]; exact this
    · rename_i hl
      simp only [hl, ite_false] at this
      exact this
  · split
    · rw [Conn.setStream_stream]; simp
    · rfl

theorem write_rel {c c₂ : Conn} {side : Side} {data : List w8} {k : Nat} {code : w64}
    (h : WriteOutcome c side data k code c₂) :
    (∀ W R, StreamRel (c.stream side) W R → StreamRel (c₂.stream side) (W ++ data.take k) R) ∧
    (∀ W R, StreamRel (c.stream (!side)) W R → StreamRel (c₂.stream (!side)) W R) ∧
    k ≤ data.length ∧ (code = errNone → k = data.length) := by
  rw [writeOutcome_iff] at h
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨fun W R hr => by simpa using hr, fun _ _ hr => hr, Nat.zero_le _,
      fun h => by simp at h⟩
  · obtain ⟨hk, hcode⟩ := h
    obtain ⟨ha, ho⟩ := writeAppend_rel c side (data.take k)
    have hb : BreakOrNot (c.writeAppend side (data.take k)) c₂ ∧
        (code = errNone → k = data.length) := by
      rcases hcode with ⟨_, hk', rfl⟩ | ⟨hc, _, rfl⟩ | ⟨hc, rfl⟩ | ⟨hc, hb⟩
      · exact ⟨.inl rfl, fun _ => hk'⟩
      · exact ⟨.inl rfl, fun h => absurd (hc.symm.trans h) (by decide)⟩
      · exact ⟨.inl rfl, fun h => absurd (hc.symm.trans h) (by decide)⟩
      · exact ⟨.inr hb, fun h => absurd (hc.symm.trans h) (by decide)⟩
    have hrel := breakOrNot_rel hb.1
    exact ⟨fun W R hr => hrel side _ R (ha W R hr),
      fun W R hr => hrel (!side) W R (by rw [ho]; exact hr), hk, hb.2⟩

theorem read_rel {c c₂ : Conn} {side : Side} {n : Nat} {data : List w8} {code : w64}
    (h : ReadOutcome c side n data code c₂) :
    c₂.stream side = c.stream side ∧ data <+: (c.stream (!side)).bytes ∧
    c₂.stream (!side) =
      { c.stream (!side) with bytes := (c.stream (!side)).bytes.drop data.length } ∧
    data.length ≤ n ∧ (code ≠ errNone → data = []) ∧ (code = errNone → n ≠ 0 → data ≠ []) := by
  unfold ReadOutcome at h
  dsimp only at h
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp_all
  rename_i hn
  rcases h with ⟨_, rfl, rfl, rfl⟩ | ⟨hne, hlen, hpre, rfl, rfl⟩ | ⟨_, _, rfl, rfl, rfl⟩ |
    ⟨_, _, rfl, hc, rfl⟩
  · simp
  · refine ⟨?_, hpre, ?_, hlen, fun h => absurd rfl h, fun _ _ => hne⟩
    · rw [Conn.setStream_stream]; simp
    · rw [Conn.setStream_stream]; simp
  · simp
  · refine ⟨rfl, List.nil_prefix, by simp, by simp, fun _ => rfl, ?_⟩
    intro h; rcases hc with rfl | rfl <;> simp at h

/-- The extension's global ghost state. -/
structure NetConnGS (GF : BundledGFunctors) where
  /-- Not an instance: under `HeapGS` the one `AllG GF` is `gooseAllG` (as `GoStateGS`). -/
  allG : AllG GF
  /-- The configured addresses (the state's `addrs`, which never change). -/
  addrs : List GoString
  /-- No configured address has a wildcard host (so `Listen` binds a configured address as
  spelled: `listenAddr_tame`). -/
  addrs_tame : ∀ a ∈ addrs, wildcardPort a = none
  /-- The names of each configured address. -/
  addrNames : GoString → AddrNames
  /-- A ghost map from connection ids to their names (persistent elements). -/
  connsName : GName
  /-- A ghost map from listener ids to their addresses (persistent elements). -/
  lisName : GName
  /-- A ghost map from connection ids to `()`: the dialers' fresh-end tokens (exclusive
  elements, `connFreshG cid false`). -/
  dialFreshName : GName
  /-- The same for the acceptors' ends (`connFreshG cid true`). -/
  acceptFreshName : GName

section ghost
variable {GF : BundledGFunctors} (hG : NetConnGS GF)

/-! ## Assertions (over the ghost state `hG`) -/

/-- `P`, stored. -/
def savedProto (γ : GName) (P : Proto GF) : IProp GF :=
  letI := hG.allG
  savedPredOwn γ .discard (fun x : w64 × List w8 => P x.1 x.2)

/-- `W` is empty or a prefix of a sequence `ext` with `□ P cid ext`. -/
def protoPrefix (P : Proto GF) (cid : w64) (W : List w8) : IProp GF :=
  iprop(⌜W = []⌝ ∨ ∃ ext, ⌜W <+: ext⌝ ∗ □ P cid ext)

/-- Half of the mono-list `γ` of bytes written: `W`. -/
def wHalf (γ : GName) (W : List w8) : IProp GF :=
  letI := hG.allG
  monoListAuthOwn γ (1 : Qp).half W

/-- `W` is a prefix of the mono-list `γ` (persistent). -/
def wLb (γ : GName) (W : List w8) : IProp GF :=
  letI := hG.allG
  monoListLbOwn γ W

/-- Half of the ghost variable `γ` of bytes read: `R`. -/
def rHalf (γ : GName) (R : List w8) : IProp GF :=
  letI := hG.allG
  ghostVar γ (1 : Qp).half R

/-- Connection `cid` has names `n`. -/
def isConnN (cid : w64) (n : ConnNames) : IProp GF :=
  letI := hG.allG
  ghostMapElem hG.connsName cid .discard n

/-- Connection `cid` exists. -/
def isConnG (cid : w64) : IProp GF := iprop(∃ n, isConnN hG cid n)

/-- The ghost map of the fresh-end tokens of the ends `side`. -/
def freshName (side : Side) : GName := if side then hG.acceptFreshName else hG.dialFreshName

/-- End `side` of connection `cid` is new: a token handed out once, by the `Dial` (`false`) or
the `Accept` (`true`) that made the end (exclusive: `connFreshG_excl`). For a client that keeps
ghost state per connection, keyed by `cid`, and must do so once per end. -/
def connFreshG (cid : w64) (side : Side) : IProp GF :=
  letI := hG.allG
  ghostMapElem (freshName hG side) cid (DFrac.own 1) ()

/-- The authorities of the fresh-end tokens: no connection outside `CN` (the connections named
so far) has one, so a new connection has both to give out. -/
def freshAuth (CN : GMap w64 ConnNames) : IProp GF :=
  letI := hG.allG
  iprop(∃ FD FA : GMap w64 Unit, ghostMapAuth (freshName hG false) 1 FD ∗
    ghostMapAuth (freshName hG true) 1 FA ∗
    ⌜∀ cid, CN !! cid = none → FD !! cid = none ∧ FA !! cid = none⌝)

/-- Listener `lid` was made by `Listen(a)`. -/
def isListenerG (lid : w64) (a : GoString) : IProp GF :=
  letI := hG.allG
  ghostMapElem hG.lisName lid .discard a

/-- The writer's half of stream `side` of a connection with names `n`. -/
def sendTokN (n : ConnNames) (side : Side) (P : Proto GF) (W : List w8) : IProp GF :=
  iprop(wHalf hG (n.get side).1 W ∗ savedProto hG (n.get side).2.2 P)

/-- The writer's half of stream `side` of `cid`: `W` written so far, protocol `P`. -/
def sendTokG (cid : w64) (side : Side) (P : Proto GF) (W : List w8) : IProp GF :=
  iprop(∃ n, isConnN hG cid n ∗ sendTokN hG n side P W)

/-- The reader's half at end `side` (reading stream `!side`) of a connection with names `n`
(`cid`). -/
def recvTokN (cid : w64) (n : ConnNames) (side : Side) (P : Proto GF) (R : List w8) :
    IProp GF :=
  iprop(rHalf hG (n.get (!side)).2.1 R ∗ savedProto hG (n.get (!side)).2.2 P ∗
    wLb hG (n.get (!side)).1 R ∗ protoPrefix P cid R)

/-- The reader's half at end `side` (reading stream `!side`): `R` read so far, protocol `P`. -/
def recvTokG (cid : w64) (side : Side) (P : Proto GF) (R : List w8) : IProp GF :=
  iprop(∃ n, isConnN hG cid n ∗ recvTokN hG cid n side P R)

/-- The bytes `bs` were written to stream `s` of `cid` (a prefix of what its writer has
written; persistent). -/
def sentLbG (cid : w64) (s : Side) (bs : List w8) : IProp GF :=
  iprop(∃ n, isConnN hG cid n ∗ wLb hG (n.get s).1 bs)

/-- Address `a` is configured, and its token. -/
def addrTokG (a : GoString) : IProp GF :=
  letI := hG.allG
  iprop(⌜a ∈ hG.addrs⌝ ∗ token (hG.addrNames a).1)

/-- Address `a` is configured, and its protocols are not set yet. -/
def addrUnsetG (a : GoString) : IProp GF :=
  letI := hG.allG
  iprop(⌜a ∈ hG.addrs⌝ ∗ savedPredOwn (hG.addrNames a).2.1 (.own 1)
      (fun _ : w64 × List w8 => iprop(True)) ∗
    savedPredOwn (hG.addrNames a).2.2 (.own 1) (fun _ : w64 × List w8 => iprop(True)))

/-- Address `a` is configured, with protocol `P` for the bytes its dialers write and `Q` for
the bytes its acceptors write (persistent). -/
def addrProtoG (a : GoString) (P Q : Proto GF) : IProp GF :=
  iprop(⌜a ∈ hG.addrs⌝ ∗ savedProto hG (hG.addrNames a).2.1 P ∗
    savedProto hG (hG.addrNames a).2.2 Q)

/-! ## The interpretation of the state -/

/-- Stream `st` of connection `cid` with names `n`: written `W`, read `R`, protocol `P`. -/
def streamInv (cid : w64) (n : StreamNames) (st : Stream) : IProp GF :=
  iprop(∃ (W R : List w8) (P : Proto GF),
    wHalf hG n.1 W ∗ rHalf hG n.2.1 R ∗ savedProto hG n.2.2 P ∗
    protoPrefix P cid W ∗ ⌜StreamRel st W R⌝)

/-- Connection `c`'s streams, with names `n`. -/
def connInvN (cid : w64) (n : ConnNames) (c : Conn) : IProp GF :=
  iprop(streamInv hG cid (n.get false) (c.stream false) ∗
    streamInv hG cid (n.get true) (c.stream true))

/-- Connection `cid`. -/
def connInv (cid : w64) (c : Conn) : IProp GF :=
  iprop(∃ n, isConnN hG cid n ∗ connInvN hG cid n c)

/-- The acceptor's end of connection `cid`, dialed to address `a`, waiting to be accepted. -/
def pendingRes (a : GoString) (cid : w64) : IProp GF :=
  iprop(∃ n, isConnN hG cid n ∗
    ⌜(n.get false).2.2 = (hG.addrNames a).2.1 ∧ (n.get true).2.2 = (hG.addrNames a).2.2⌝ ∗
    wHalf hG (n.get true).1 [] ∗ rHalf hG (n.get false).2.1 [] ∗ connFreshG hG cid true)

/-- Listener `lid`: if open, the acceptor's ends of its pending connections. -/
def lisInv (l : Listener) : IProp GF :=
  if l.isOpen then iprop([∗list] cid ∈ l.pending, pendingRes hG l.addr cid) else iprop(True)

/-- The interpretation of the extension's global state. -/
def netCtx (g : NetState) : IProp GF :=
  letI := hG.allG
  iprop(⌜g.addrs = hG.addrs⌝ ∗
    (∃ CN : GMap w64 ConnNames, ghostMapAuth hG.connsName 1 CN ∗
      ⌜∀ cid, (CN !! cid).isSome = (g.conns !! cid).isSome⌝ ∗ freshAuth hG CN) ∗
    (∃ LN : GMap w64 GoString, ghostMapAuth hG.lisName 1 LN ∗
      ⌜∀ lid, LN !! lid = (g.listeners !! lid).map (·.addr)⌝) ∗
    ([∗map] cid ↦ c ∈ g.conns, connInv hG cid c) ∗
    ([∗map] _lid ↦ l ∈ g.listeners, lisInv hG l))

/-- The start resources of the network `g`: each configured address's token and unset
protocols. -/
def netStart (g : NetState) : IProp GF :=
  iprop([∗list] a ∈ g.addrs, addrTokG hG a ∗ addrUnsetG hG a)

end ghost

/-! ## Allocation -/

section alloc
variable {GF : BundledGFunctors} [AllG GF]

/-- The fresh resources of an address with names `n`. -/
def addrFresh (n : AddrNames) : IProp GF :=
  iprop(token n.1 ∗ savedPredOwn n.2.1 (.own 1) (fun _ : w64 × List w8 => iprop(True)) ∗
    savedPredOwn n.2.2 (.own 1) (fun _ : w64 × List w8 => iprop(True)))

theorem addrFresh_alloc : ⊢ |==> ∃ n : AddrNames, addrFresh (GF := GF) n := by
  imod token_alloc (GF := GF) with ⟨%γ1, H1⟩
  imod saved_pred_alloc (GF := GF) (fun _ : w64 × List w8 => iprop(True)) (.own 1)
    DFrac.valid_own_one with ⟨%γ2, H2⟩
  imod saved_pred_alloc (GF := GF) (fun _ : w64 × List w8 => iprop(True)) (.own 1)
    DFrac.valid_own_one with ⟨%γ3, H3⟩
  imodintro
  iexists (γ1, γ2, γ3)
  unfold addrFresh
  iframe

/-- Fresh names and resources for each of a list of distinct addresses. -/
theorem addrs_alloc : ∀ (l : List GoString), l.Nodup →
    ⊢ |==> ∃ f : GoString → AddrNames, [∗list] a ∈ l, addrFresh (GF := GF) (f a)
  | [], _ => by
    iapply bupd_intro
    iexists (fun _ => ((0 : GName), (0 : GName), (0 : GName)))
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | a :: l, hl => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    imod addrs_alloc l hl with ⟨%f, Hl⟩
    imod addrFresh_alloc (GF := GF) with ⟨%n, Ha⟩
    imodintro
    iexists (fun x => if x = a then n else f x)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · simp only [ite_true]; iexact Ha
    · iapply BigSepL.bigSepL_mono (Φ := fun _ x => addrFresh (GF := GF) (f x)) ?_ $$ Hl
      intro k x hx
      have : x ≠ a := fun h => ha (h ▸ List.mem_of_getElem? hx)
      simp only [this, ite_false]
      exact .rfl

end alloc

section init
variable {GF : BundledGFunctors}

/-- The ghost state of the network `g` with no listener and no connection, and its start
resources. -/
theorem net_global_init (hA : AllG GF) (g : NetState) (hl : g.listeners = ∅)
    (hc : g.conns = ∅) (hn : g.addrs.Nodup) (ht : ∀ a ∈ g.addrs, wildcardPort a = none) :
    ⊢@{IProp GF} |==> ∃ hG : NetConnGS GF, netCtx hG g ∗ netStart hG g := by
  imod addrs_alloc (GF := GF) g.addrs hn with ⟨%f, Ha⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := ConnNames) with ⟨%γc, Hc⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := GoString) with ⟨%γl, Hl⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γd, HFD⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γa, HFA⟩
  imodintro
  iexists ⟨hA, g.addrs, ht, f, γc, γl, γd, γa⟩
  isplitl [Hc Hl HFD HFA]
  · unfold netCtx
    simp only [hl, hc]
    isplitr
    · ipureintro; simp
    isplitl [Hc HFD HFA]
    · iexists ∅
      iframe Hc
      isplitr
      · ipureintro; intro cid; simp
      unfold freshAuth freshName
      simp only [Bool.false_eq_true, ite_false, ite_true]
      iexists ∅, ∅
      iframe HFD HFA
      ipureintro; intro cid _; exact ⟨rfl, rfl⟩
    isplitl [Hl]
    · iexists ∅
      iframe Hl
      ipureintro; intro lid; simp
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; iempintro
    · iapply BigSepM.bigSepM_empty.2; iempintro
  · unfold netStart
    iapply BigSepL.bigSepL_mono ?_ $$ Ha
    intro k a hk
    have hmem : a ∈ g.addrs := List.mem_of_getElem? hk
    unfold addrFresh addrTokG addrUnsetG
    iintro ⟨Ht, H1, H2⟩
    isplitl [Ht]
    · isplitr
      · ipureintro; exact hmem
      · iexact Ht
    · isplitr
      · ipureintro; exact hmem
      · iframe

end init


/-! ## Ghost-state lemmas -/

section monoHalves
variable {GF : BundledGFunctors} [AllG GF]

theorem monoList_halves (γ : GName) (W : List w8) :
    monoListAuthOwn (GF := GF) γ 1 W ⊣⊢
      monoListAuthOwn γ (1 : Qp).half W ∗ monoListAuthOwn γ (1 : Qp).half W := by
  have := (monoListAuthOwn_fractional (GF := GF) γ W).fractional (1 : Qp).half (1 : Qp).half
  rwa [Qp.half_add_half] at this

theorem monoList_halves_update (γ : GName) {W W' : List w8} (h : W <+: W') :
    ⊢ monoListAuthOwn (GF := GF) γ (1 : Qp).half W -∗ monoListAuthOwn γ (1 : Qp).half W ==∗
      monoListAuthOwn γ (1 : Qp).half W' ∗ monoListAuthOwn γ (1 : Qp).half W' ∗
      monoListLbOwn γ W' := by
  iintro H1 H2
  ihave H := (monoList_halves (GF := GF) γ W).2 $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  imod monoListAuthOwn_update W' h $$ H with ⟨H, #Hlb⟩
  ihave ⟨H1, H2⟩ := (monoList_halves (GF := GF) γ W').1 $$ H
  imodintro
  iframe
  iexact Hlb

end monoHalves

section ghostLemmas
variable {GF : BundledGFunctors} (hG : NetConnGS GF)

theorem isConnN_agree (cid : w64) (n1 n2 : ConnNames) :
    ⊢ isConnN hG cid n1 -∗ isConnN hG cid n2 -∗ ⌜n1 = n2⌝ := by
  letI := hG.allG
  unfold isConnN
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

instance isConnN_persistent (cid : w64) (n : ConnNames) : Persistent (isConnN hG cid n) := by
  letI := hG.allG
  unfold isConnN; infer_instance

instance savedProto_persistent (γ : GName) (P : Proto GF) : Persistent (savedProto hG γ P) := by
  letI := hG.allG
  unfold savedProto; infer_instance

instance protoPrefix_persistent (P : Proto GF) (cid : w64) (W : List w8) :
    Persistent (protoPrefix P cid W) := by
  unfold protoPrefix; infer_instance

instance isConnG_persistent (cid : w64) : Persistent (isConnG hG cid) := by
  unfold isConnG; infer_instance

instance isListenerG_persistent (lid : w64) (a : GoString) :
    Persistent (isListenerG hG lid a) := by
  letI := hG.allG
  unfold isListenerG; infer_instance

/-- A connection named in the ghost state exists. -/
theorem netCtx_conn (g : NetState) (cid : w64) (n : ConnNames) :
    ⊢ netCtx hG g -∗ isConnN hG cid n -∗ ⌜∃ c, g.conns !! cid = some c⌝ ∗ netCtx hG g := by
  letI := hG.allG
  iintro Hg #Hn
  unfold netCtx
  icases Hg with ⟨%Ha, ⟨%CN, HCN, %HCNd, HF⟩, HL, Hc, Hl⟩
  unfold isConnN
  ihave %Hlk := ghost_map_lookup $$ HCN Hn
  isplitr
  · ipureintro
    have := HCNd cid
    rw [show CN !! cid = some n from Hlk] at this
    cases h : g.conns !! cid with
    | none => rw [h] at this; simp at this
    | some c => exact ⟨c, rfl⟩
  · isplitr
    · ipureintro; exact Ha
    isplitl [HCN HF]
    · iexists CN
      iframe HCN HF
      ipureintro; exact HCNd
    iframe

/-- Access to connection `cid` in the interpretation, to put back a new state of it. -/
theorem netCtx_conn_acc (g : NetState) (cid : w64) (n : ConnNames) :
    ⊢ netCtx hG g -∗ isConnN hG cid n -∗ ∃ c, ⌜g.conns !! cid = some c⌝ ∗
      connInvN hG cid n c ∗ ∀ c', connInvN hG cid n c' -∗ netCtx hG (g.setConn cid c') := by
  letI := hG.allG
  iintro Hg #Hn
  unfold netCtx
  icases Hg with ⟨%Ha, ⟨%CN, HCN, %HCNd, HF⟩, HL, Hc, Hl⟩
  ihave %Hlk := ghost_map_lookup $$ HCN [Hn]
  · unfold isConnN; iexact Hn
  obtain ⟨c, hc⟩ : ∃ c, g.conns !! cid = some c := by
    have := HCNd cid
    rw [show CN !! cid = some n from Hlk] at this
    cases h : g.conns !! cid with
    | none => rw [h] at this; simp at this
    | some c => exact ⟨c, rfl⟩
  icases BigSepM.bigSepM_insert_acc hc $$ Hc with ⟨Hci, Hclose⟩
  unfold connInv
  icases Hci with ⟨%n', #Hn', Hci⟩
  ihave %Heq := isConnN_agree hG cid n n' $$ Hn Hn'
  subst Heq
  iexists c
  isplitr
  · ipureintro; exact hc
  iframe Hci
  iintro %c' Hc'
  unfold NetState.setConn
  isplitr
  · ipureintro; exact Ha
  isplitl [HCN HF]
  · iexists CN
    iframe HCN HF
    ipureintro
    intro cid'
    rw [HCNd cid']
    by_cases h : cid = cid'
    · subst h; simp [hc]
    · simp [h]
  iframe HL Hl
  iapply Hclose
  iexists n
  iframe Hn Hc'

theorem streamInv_mono (cid : w64) (nm : StreamNames) {st st' : Stream}
    (h : ∀ W R, StreamRel st W R → StreamRel st' W R) :
    streamInv hG cid nm st ⊢ streamInv hG cid nm st' := by
  letI := hG.allG
  unfold streamInv
  iintro ⟨%W, %R, %P, H1, H2, H3, H4, %H5⟩
  iexists W, R, P
  iframe
  ipureintro; exact h W R H5

theorem connInvN_mono (cid : w64) (n : ConnNames) {c c' : Conn}
    (h : ∀ s W R, StreamRel (c.stream s) W R → StreamRel (c'.stream s) W R) :
    connInvN hG cid n c ⊢ connInvN hG cid n c' := by
  unfold connInvN
  iintro ⟨H1, H2⟩
  isplitl [H1]
  · iapply streamInv_mono hG cid _ (h false) $$ H1
  · iapply streamInv_mono hG cid _ (h true) $$ H2

instance wLb_persistent (γ : GName) (W : List w8) : Persistent (wLb hG γ W) := by
  letI := hG.allG
  unfold wLb; infer_instance

instance sentLbG_persistent (cid : w64) (s : Side) (bs : List w8) :
    Persistent (sentLbG hG cid s bs) := by
  unfold sentLbG; infer_instance

theorem wHalf_agree (γ : GName) (W1 W2 : List w8) :
    ⊢ wHalf hG γ W1 -∗ wHalf hG γ W2 -∗ ⌜W1 = W2⌝ ∗ wHalf hG γ W1 ∗ wHalf hG γ W2 := by
  refine entails_wand (wand_intro (persistent_entails_right ?_))
  letI := hG.allG
  unfold wHalf
  iintro ⟨H1, H2⟩
  ihave %h := monoListAuthOwn_agree γ _ _ W1 W2 $$ H1 H2
  ipureintro; exact h.2

theorem rHalf_agree (γ : GName) (R1 R2 : List w8) :
    ⊢ rHalf hG γ R1 -∗ rHalf hG γ R2 -∗ ⌜R1 = R2⌝ ∗ rHalf hG γ R1 ∗ rHalf hG γ R2 := by
  refine entails_wand (wand_intro (persistent_entails_right ?_))
  letI := hG.allG
  unfold rHalf
  iintro ⟨H1, H2⟩
  iapply ghostVar_agree $$ H1 H2

theorem wHalf_update (γ : GName) {W W' : List w8} (h : W <+: W') :
    ⊢ wHalf hG γ W -∗ wHalf hG γ W ==∗ wHalf hG γ W' ∗ wHalf hG γ W' ∗ wLb hG γ W' := by
  letI := hG.allG
  unfold wHalf wLb
  exact monoList_halves_update γ h

theorem rHalf_update (γ : GName) (R1 R2 R : List w8) :
    ⊢ rHalf hG γ R1 -∗ rHalf hG γ R2 ==∗ rHalf hG γ R ∗ rHalf hG γ R := by
  letI := hG.allG
  unfold rHalf
  exact ghostVar_update_halves R γ R1 R2

theorem wHalf_lb (γ : GName) {W W' : List w8} (h : W' <+: W) :
    wHalf hG γ W ⊢ wHalf hG γ W ∗ wLb hG γ W' := by
  refine persistent_entails_left ?_
  letI := hG.allG
  unfold wHalf wLb
  exact (monoListLbOwn_get γ _ W).trans (monoListLbOwn_le W' h)

theorem savedProto_agree (γ : GName) (P1 P2 : Proto GF) (cid : w64) (ext : List w8) :
    ⊢ savedProto hG γ P1 -∗ savedProto hG γ P2 -∗ ▷ (P1 cid ext ≡ P2 cid ext) := by
  letI := hG.allG
  unfold savedProto
  exact saved_pred_agree γ _ _ (fun x : w64 × List w8 => P1 x.1 x.2)
    (fun x : w64 × List w8 => P2 x.1 x.2) (cid, ext)

theorem box_eq_rewrite {A B : IProp GF} : ⊢ (A ≡ B) -∗ □ A -∗ □ B := by
  iintro #Heq #HA
  ihave #Hiff := internalEq_iff A B $$ Heq
  imodintro
  icases Hiff with ⟨H1, -⟩
  iapply H1
  iexact HA

theorem connInvN_side (cid : w64) (n : ConnNames) (c : Conn) (s : Side) :
    connInvN hG cid n c ⊣⊢
      streamInv hG cid (n.get s) (c.stream s) ∗ streamInv hG cid (n.get (!s)) (c.stream (!s)) := by
  cases s
  · exact .rfl
  · exact sep_comm

theorem streamInv_write (cid : w64) (nm : StreamNames) {st st' : Stream} {W d data : List w8}
    {P : Proto GF} (hrel : ∀ W' R, StreamRel st W' R → StreamRel st' (W' ++ d) R)
    (hd : d <+: data) :
    ⊢ streamInv hG cid nm st -∗ wHalf hG nm.1 W -∗ savedProto hG nm.2.2 P -∗ □ P cid (W ++ data)
      ==∗ streamInv hG cid nm st' ∗ wHalf hG nm.1 (W ++ d) := by
  iintro Hs Hw #HP #HPd
  unfold streamInv
  icases Hs with ⟨%W', %R, %P', Hw', Hr, -, -, %Hrel⟩
  ihave ⟨%Heq, Hw, Hw'⟩ := wHalf_agree hG _ W W' $$ Hw Hw'
  subst Heq
  imod wHalf_update hG nm.1 (List.prefix_append W d) $$ Hw Hw' with ⟨Hw, Hw', -⟩
  imodintro
  isplitr [Hw]
  · iexists (W ++ d), R, P
    isplitl [Hw']
    · iexact Hw'
    isplitl [Hr]
    · iexact Hr
    isplitr
    · iexact HP
    isplitr
    · unfold protoPrefix
      iright
      iexists (W ++ data)
      isplitr
      · ipureintro; exact (List.prefix_append_right_inj W).2 hd
      · iexact HPd
    · ipureintro; exact hrel W R Hrel
  · iexact Hw

theorem streamInv_read (cid : w64) (nm : StreamNames) {st : Stream} {R data : List w8}
    {P : Proto GF} (hd : data <+: st.bytes) :
    ⊢ streamInv hG cid nm st -∗ rHalf hG nm.2.1 R -∗ savedProto hG nm.2.2 P ==∗
      streamInv hG cid nm { st with bytes := st.bytes.drop data.length } ∗
      rHalf hG nm.2.1 (R ++ data) ∗ wLb hG nm.1 (R ++ data) ∗
      ▷ protoPrefix P cid (R ++ data) := by
  iintro Hs Hr #HP
  unfold streamInv
  icases Hs with ⟨%W, %R', %P', Hw, Hr', #HP', #Hpp, %Hrel⟩
  ihave ⟨%Heq, Hr, Hr'⟩ := rHalf_agree hG _ R R' $$ Hr Hr'
  subst Heq
  have Hrel' := Hrel.read hd
  imod rHalf_update hG _ R R (R ++ data) $$ Hr Hr' with ⟨Hr, Hr'⟩
  ihave ⟨Hw, #Hlb⟩ := wHalf_lb hG nm.1 Hrel'.1 $$ Hw
  ihave Hpre : ▷ protoPrefix P cid (R ++ data) $$ []
  · unfold protoPrefix
    icases Hpp with (%hW | ⟨%ext, %hext, #HPe⟩)
    · inext
      ileft
      ipureintro
      have := Hrel'.1
      rw [hW] at this
      exact List.prefix_nil.mp this
    · ihave #Hag := savedProto_agree hG nm.2.2 P' P cid ext $$ HP' HP
      inext
      iright
      iexists ext
      isplitr
      · ipureintro; exact Hrel'.1.trans hext
      · iapply box_eq_rewrite $$ Hag HPe
  imodintro
  isplitr [Hr Hpre]
  · iexists W, (R ++ data), P'
    isplitl [Hw]
    · iexact Hw
    isplitl [Hr']
    · iexact Hr'
    isplitr
    · iexact HP'
    isplitr
    · iexact Hpp
    · ipureintro; exact Hrel'
  · iframe
    iexact Hlb

theorem connInvN_write {c c₂ : Conn} {side : Side} {data : List w8} {k : Nat} {code : w64}
    (hw : WriteOutcome c side data k code c₂) (cid : w64) (n : ConnNames) (P : Proto GF)
    (W : List w8) :
    ⊢ connInvN hG cid n c -∗ sendTokN hG n side P W -∗ □ P cid (W ++ data) ==∗
      connInvN hG cid n c₂ ∗ sendTokN hG n side P (W ++ data.take k) := by
  obtain ⟨hrel, hother, -, -⟩ := write_rel hw
  iintro Hc Htok #HPd
  unfold sendTokN
  icases Htok with ⟨Hw, #HP⟩
  ihave ⟨Hs, Ho⟩ := (connInvN_side hG cid n c side).1 $$ Hc
  imod streamInv_write hG cid _ hrel (List.take_prefix k data) $$ Hs Hw HP HPd with ⟨Hs, Hw⟩
  ihave Ho := streamInv_mono hG cid _ hother $$ Ho
  imodintro
  isplitl [Hs Ho]
  · iapply (connInvN_side hG cid n c₂ side).2
    iframe
  · iframe
    iexact HP

theorem connInvN_read {c c₂ : Conn} {side : Side} {m : Nat} {data : List w8} {code : w64}
    (hr : ReadOutcome c side m data code c₂) (cid : w64) (n : ConnNames) (P : Proto GF)
    (R : List w8) :
    ⊢ connInvN hG cid n c -∗ recvTokN hG cid n side P R ==∗
      connInvN hG cid n c₂ ∗ ▷ recvTokN hG cid n side P (R ++ data) := by
  obtain ⟨hsame, hd, hother, -⟩ := read_rel hr
  iintro Hc Htok
  unfold recvTokN
  icases Htok with ⟨Hr, #HP, -, -⟩
  ihave ⟨Ho, Hs⟩ := (connInvN_side hG cid n c side).1 $$ Hc
  imod streamInv_read hG cid _ hd $$ Hs Hr HP with ⟨Hs, Hr, #Hlb, Hpre⟩
  imodintro
  isplitl [Hs Ho]
  · iapply (connInvN_side hG cid n c₂ side).2
    rw [hsame, hother]
    iframe
  · inext
    iframe
    isplitr
    · iexact HP
    · iexact Hlb

/-- Set the protocols of an address (once, typically in the client's start-up update). -/
theorem addr_set_proto (a : GoString) (P Q : Proto GF) :
    ⊢ addrUnsetG hG a ==∗ addrProtoG hG a P Q := by
  letI := hG.allG
  unfold addrUnsetG addrProtoG savedProto
  iintro ⟨%h, H1, H2⟩
  imod saved_pred_update (fun x : w64 × List w8 => P x.1 x.2) _ _ $$ H1 with H1
  imod saved_pred_persist _ _ _ $$ H1 with H1
  imod saved_pred_update (fun x : w64 × List w8 => Q x.1 x.2) _ _ $$ H2 with H2
  imod saved_pred_persist _ _ _ $$ H2 with H2
  imodintro
  isplitr
  · ipureintro; exact h
  · iframe

instance addrProtoG_persistent (a : GoString) (P Q : Proto GF) :
    Persistent (addrProtoG hG a P Q) := by
  unfold addrProtoG; infer_instance

theorem netCtx_addrs (g : NetState) :
    ⊢ netCtx hG g -∗ ⌜g.addrs = hG.addrs⌝ ∗ netCtx hG g := by
  refine entails_wand (persistent_entails_right ?_)
  letI := hG.allG
  unfold netCtx
  iintro ⟨%Ha, -⟩
  ipureintro; exact Ha

theorem netCtx_listener (g : NetState) (lid : w64) (a : GoString) :
    ⊢ netCtx hG g -∗ isListenerG hG lid a -∗
      ⌜∃ l, g.listeners !! lid = some l ∧ l.addr = a⌝ ∗ (netCtx hG g ∗ isListenerG hG lid a) := by
  refine entails_wand (wand_intro (persistent_entails_right ?_))
  letI := hG.allG
  unfold netCtx isListenerG
  iintro ⟨⟨%Ha, HC, ⟨%LN, HLN, %HLNd⟩, Hc, Hl⟩, Hlis⟩
  ihave %Hlk := ghost_map_lookup $$ HLN Hlis
  ipureintro
  have := HLNd lid
  rw [show LN !! lid = some a from Hlk] at this
  cases h : g.listeners !! lid with
  | none => rw [h] at this; simp at this
  | some l => rw [h] at this; simp at this; exact ⟨l, rfl, this.symm⟩

theorem netCtx_listen (g : NetState) (lid : w64) (a : GoString)
    (hfresh : g.listeners !! lid = none) :
    ⊢ netCtx hG g ==∗
      netCtx hG { g with listeners := <[lid := ⟨a, true, []⟩]> g.listeners } ∗
      isListenerG hG lid a := by
  letI := hG.allG
  iintro Hg
  unfold netCtx
  icases Hg with ⟨%Ha, HC, ⟨%LN, HLN, %HLNd⟩, Hc, Hl⟩
  have hLN : LN.lookup lid = none := by
    have := HLNd lid; rw [hfresh] at this; exact this
  imod ghost_map_insert_persist lid a hLN $$ HLN with ⟨HLN, #Hlis⟩
  imodintro
  isplitl [HC HLN Hc Hl]
  · isplitr
    · ipureintro; exact Ha
    isplitl [HC]
    · iexact HC
    isplitl [HLN]
    · iexists (LN.insert lid a)
      iframe HLN
      ipureintro
      intro lid'
      by_cases h : lid = lid'
      · subst h; simp
      · rw [GMap.lookup_insert_ne _ _ h]
        have := HLNd lid'
        simp only [GMap.lookup_insert_ne _ _ h]
        exact this
    isplitl [Hc]
    · iexact Hc
    · iapply (BigSepM.bigSepM_insert hfresh).2
      iframe Hl
      unfold lisInv
      simp only [ite_true]
      iapply BigSepL.bigSepL_nil.2
      iempintro
  · unfold isListenerG
    iexact Hlis

theorem netCtx_closeListener (g : NetState) (lid : w64) (l : Listener)
    (hl : g.listeners !! lid = some l) :
    netCtx hG g ⊢ netCtx hG
      { g with listeners := <[lid := { l with isOpen := false, pending := [] }]> g.listeners } := by
  letI := hG.allG
  unfold netCtx
  iintro ⟨%Ha, HC, ⟨%LN, HLN, %HLNd⟩, Hc, Hl⟩
  icases BigSepM.bigSepM_insert_acc hl $$ Hl with ⟨-, Hclose⟩
  isplitr
  · ipureintro; exact Ha
  isplitl [HC]
  · iexact HC
  isplitl [HLN]
  · iexists LN
    iframe HLN
    ipureintro
    intro lid'
    rw [HLNd lid']
    by_cases h : lid = lid'
    · subst h; simp [hl]
    · simp [h]
  isplitl [Hc]
  · iexact Hc
  · iapply Hclose
    unfold lisInv
    simp only [Bool.false_eq_true, ite_false]
    itrivial

theorem netCtx_accept (g : NetState) (lid : w64) (l : Listener) (cid : w64) (a : GoString)
    (P Q : Proto GF) (hl : g.listeners !! lid = some l) (hopen : l.isOpen = true)
    (haddr : l.addr = a) (hcid : cid ∈ l.pending) :
    ⊢ netCtx hG g -∗ addrProtoG hG a P Q ==∗
      netCtx hG { g with listeners :=
        <[lid := { l with pending := l.pending.erase cid }]> g.listeners } ∗
      sendTokG hG cid true Q [] ∗ recvTokG hG cid true P [] ∗ connFreshG hG cid true := by
  letI := hG.allG
  iintro Hg #Hpr
  unfold netCtx
  icases Hg with ⟨%Ha, HC, ⟨%LN, HLN, %HLNd⟩, Hc, Hl⟩
  icases BigSepM.bigSepM_insert_acc hl $$ Hl with ⟨Hli, Hclose⟩
  unfold lisInv
  simp only [hopen, ite_true]
  ihave Hli := (BigSepL.bigSepL_perm (Φ := fun c => pendingRes hG l.addr c)
    (List.perm_cons_erase hcid)).1 $$ Hli
  icases BigSepL.bigSepL_cons.1 $$ Hli with ⟨Hp, Hrest⟩
  unfold pendingRes
  icases Hp with ⟨%n, #Hn, %he, Hw, Hr, Hf⟩
  imod monoListLbOwn_nil (GF := GF) (A := w8) (n.get false).1 with #Hlb
  unfold addrProtoG
  icases Hpr with ⟨%hin, #HP, #HQ⟩
  imodintro
  isplitl [HC HLN Hc Hclose Hrest]
  · isplitr
    · ipureintro; exact Ha
    isplitl [HC]
    · iexact HC
    isplitl [HLN]
    · iexists LN
      iframe HLN
      ipureintro
      intro lid'
      rw [HLNd lid']
      by_cases h : lid = lid'
      · subst h; simp [hl]
      · simp [h]
    isplitl [Hc]
    · iexact Hc
    · iapply Hclose
      dsimp only
      simp only [ite_true]
      iexact Hrest
  · subst haddr
    isplitl [Hw]
    · unfold sendTokG sendTokN
      iexists n
      iframe Hn Hw
      rw [he.2]
      iexact HQ
    isplitl [Hr]
    · unfold recvTokG recvTokN
      iexists n
      simp only [Bool.not_true]
      iframe Hn Hr
      isplitr
      · rw [he.1]; iexact HP
      isplitr
      · unfold wLb; iexact Hlb
      · unfold protoPrefix; ileft; ipureintro; rfl
    · iexact Hf

theorem streamRel_fresh (s : Side) : StreamRel (Conn.fresh.stream s) [] [] := by
  simp [StreamRel, Conn.fresh]

/-- The connection a failed `Dial` may leave pending has empty streams. -/
theorem streamRel_abandoned (s : Side) : StreamRel (Conn.abandoned.stream s) [] [] := by
  cases s <;> simp [StreamRel, Conn.abandoned]

/-- A new connection `c₀` with empty streams (`Conn.fresh`, or `Conn.abandoned`), pending at
listener `lid`: the acceptor's end waits there, the dialer's end is returned (and dropped by a
`Dial` that failed). -/
theorem netCtx_dial (g : NetState) (lid : w64) (l : Listener) (cid : w64) (a : GoString)
    (P Q : Proto GF) (c₀ : Conn) (hc₀ : ∀ s, StreamRel (c₀.stream s) [] [])
    (hl : g.listeners !! lid = some l) (hopen : l.isOpen = true)
    (haddr : l.addr = a) (hfresh : g.conns !! cid = none) :
    ⊢ netCtx hG g -∗ addrProtoG hG a P Q ==∗
      netCtx hG { g with
        listeners := <[lid := { l with pending := l.pending ++ [cid] }]> g.listeners,
        conns := <[cid := c₀]> g.conns } ∗
      sendTokG hG cid false P [] ∗ recvTokG hG cid false Q [] ∗ connFreshG hG cid false := by
  letI := hG.allG
  iintro Hg #Hpr
  unfold netCtx
  icases Hg with ⟨%Ha, ⟨%CN, HCN, %HCNd, HF⟩, ⟨%LN, HLN, %HLNd⟩, Hc, Hl⟩
  have hCN : CN.lookup cid = none := by
    have := HCNd cid
    rw [hfresh] at this
    show CN !! cid = none
    cases h : CN !! cid with
    | none => rfl
    | some _ => rw [h] at this; simp at this
  unfold freshAuth
  icases HF with ⟨%FD, %FA, HFD, HFA, %HFd⟩
  obtain ⟨hFD, hFA⟩ := HFd cid hCN
  imod ghost_map_insert cid () hFD $$ HFD with ⟨HFD, HfD⟩
  imod ghost_map_insert cid () hFA $$ HFA with ⟨HFA, HfA⟩
  imod mono_list_own_alloc (GF := GF) ([] : List w8) with ⟨%γW0, HW0, -⟩
  imod mono_list_own_alloc (GF := GF) ([] : List w8) with ⟨%γW1, HW1, #HlbW1⟩
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γR0, HR0⟩
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γR1, HR1⟩
  ihave ⟨HW0a, HW0b⟩ := (monoList_halves (GF := GF) γW0 []).1 $$ HW0
  ihave ⟨HW1a, HW1b⟩ := (monoList_halves (GF := GF) γW1 []).1 $$ HW1
  ihave ⟨HR0a, HR0b⟩ := (ghostVar_split_half (GF := GF) γR0 1 ([] : List w8)).1 $$ HR0
  ihave ⟨HR1a, HR1b⟩ := (ghostVar_split_half (GF := GF) γR1 1 ([] : List w8)).1 $$ HR1
  imod ghost_map_insert_persist cid
    (((γW0, γR0, (hG.addrNames a).2.1), (γW1, γR1, (hG.addrNames a).2.2)) : ConnNames)
    hCN $$ HCN with ⟨HCN, #Hn⟩
  unfold addrProtoG
  icases Hpr with ⟨%hin, #HP, #HQ⟩
  icases BigSepM.bigSepM_insert_acc hl $$ Hl with ⟨Hli, Hclose⟩
  imodintro
  isplitl [HCN HFD HFA HLN Hc Hli Hclose HW0a HW1a HR0a HR1a HW1b HR0b HfA]
  · isplitr
    · ipureintro; exact Ha
    isplitl [HCN HFD HFA]
    · iexists _
      iframe HCN
      isplitr
      · ipureintro
        intro cid'
        by_cases h : cid = cid'
        · subst h; simp
        · simp [h, HCNd cid']
      iexists _, _
      iframe HFD HFA
      ipureintro
      intro cid' hn
      by_cases h : cid = cid'
      · subst h; simp at hn
      · have hn' : CN !! cid' = none := by simpa [h] using hn
        have := HFd cid' hn'
        simpa [h] using this
    isplitl [HLN]
    · iexists LN
      iframe HLN
      ipureintro
      intro lid'
      rw [HLNd lid']
      by_cases h : lid = lid'
      · subst h; simp [hl]
      · simp [h]
    isplitl [Hc HW0a HW1a HR0a HR1a]
    · iapply (BigSepM.bigSepM_insert hfresh).2
      iframe Hc
      unfold connInv connInvN streamInv isConnN
      iexists _
      iframe Hn
      simp only [ConnNames.get_false, ConnNames.get_true]
      isplitl [HW0a HR0a]
      · iexists [], [], P
        unfold wHalf rHalf
        iframe HW0a HR0a
        isplitr
        · iexact HP
        isplitr
        · unfold protoPrefix; ileft; ipureintro; rfl
        · ipureintro; exact hc₀ false
      · iexists [], [], Q
        unfold wHalf rHalf
        iframe HW1a HR1a
        isplitr
        · iexact HQ
        isplitr
        · unfold protoPrefix; ileft; ipureintro; rfl
        · ipureintro; exact hc₀ true
    · iapply Hclose
      unfold lisInv
      dsimp only
      simp only [hopen, ite_true]
      iapply BigSepL.bigSepL_snoc.2
      iframe Hli
      unfold pendingRes isConnN
      iexists _
      iframe Hn
      simp only [ConnNames.get_false, ConnNames.get_true]
      isplitr
      · ipureintro; rw [haddr]; exact ⟨rfl, rfl⟩
      unfold wHalf rHalf connFreshG
      iframe
  · isplitl [HW0b]
    · unfold sendTokG sendTokN isConnN
      iexists _
      iframe Hn
      simp only [ConnNames.get_false]
      unfold wHalf
      iframe HW0b
      iexact HP
    isplitl [HR1b]
    · unfold recvTokG recvTokN isConnN
      iexists _
      iframe Hn
      simp only [Bool.not_false, ConnNames.get_true]
      unfold rHalf wLb
      iframe HR1b
      isplitr
      · iexact HQ
      isplitr
      · iexact HlbW1
      · unfold protoPrefix; ileft; ipureintro; rfl
    · unfold connFreshG; iexact HfD

instance connFreshG_timeless (cid : w64) (side : Side) : Timeless (connFreshG hG cid side) := by
  letI := hG.allG
  unfold connFreshG; infer_instance

/-- An end is new at most once. -/
theorem connFreshG_excl (cid : w64) (side : Side) :
    connFreshG hG cid side ∗ connFreshG hG cid side ⊢ (False : IProp GF) := by
  letI := hG.allG
  unfold connFreshG
  iintro ⟨H1, H2⟩
  icases ghostMapElem_ne (freshName hG side) cid cid _ () () $$ H1 H2 with %Hne
  exact absurd rfl Hne

end ghostLemmas

/-- A node's ghost state: its IP (the extension's local state, which never changes), as data. -/
structure NetConnNodeGS (GF : BundledGFunctors) where
  ip : GoString

/-- The ghost state of the extension. The program gets, for each configured address, its token
and its unset protocols; each node, the knowledge of its IP (`nodeIp`, as Perennial's network
extension gives a node its address). -/
instance netConn_interp : ExtInterp netConnExt where
  LocalGS := NetConnNodeGS
  GlobalGS := NetConnGS
  localCtx hL me := iprop(⌜me = hL.ip⌝)
  globalCtx := netCtx
  PreG GF := AllG GF
  initgP g := g.listeners = ∅ ∧ g.conns = ∅ ∧ g.addrs.Nodup ∧
    ∀ a ∈ g.addrs, wildcardPort a = none
  initP _ _ := True
  globalStart := netStart
  localStart hL me := iprop(⌜hL.ip = me⌝)
  global_init _ hPre g h := net_global_init hPre g h.1 h.2.1 h.2.2.1 h.2.2.2
  local_init _ _ me _ _ := by
    iapply bupd_intro
    iexists (⟨me⟩ : NetConnNodeGS _)
    isplit <;> ipureintro <;> rfl

/-! ## Wildcard hosts -/

/-- A wildcard host followed by `":" ++ port` has the port `port`. -/
theorem wildcardPort_wild (h port : GoString) (hh : h ∈ wildcardHosts) :
    wildcardPort (h ++ go!":" ++ port) = some port := by
  simp only [wildcardHosts, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl <;>
    simp [wildcardPort, wildcardHosts, List.find?, List.isPrefixOf]

/-- A wildcard host resolves to the node's own address. -/
theorem listenAddr_wild (me h port : GoString) (hh : h ∈ wildcardHosts) :
    listenAddr me (h ++ go!":" ++ port) = me ++ go!":" ++ port := by
  simp only [listenAddr, wildcardPort_wild h port hh]

/-- An address with no wildcard host is bound as spelled. -/
theorem listenAddr_tame (me a : GoString) (h : wildcardPort a = none) : listenAddr me a = a := by
  simp only [listenAddr, h]

/-- An address whose first byte is none of `':'`, `'0'`, `'['` has no wildcard host. -/
theorem wildcardPort_head (c : w8) (rest : GoString) (h1 : c ≠ 58#8) (h2 : c ≠ 48#8)
    (h3 : c ≠ 91#8) : wildcardPort (c :: rest) = none := by
  have e1 : (58#8 == c) = false := beq_false_of_ne (Ne.symm h1)
  have e2 : (48#8 == c) = false := beq_false_of_ne (Ne.symm h2)
  have e3 : (91#8 == c) = false := beq_false_of_ne (Ne.symm h3)
  simp [wildcardPort, wildcardHosts, List.find?, List.isPrefixOf, e1, e2, e3]

/-! ## Specs -/

section progress

theorem read_progress (c : Conn) (side : Side) (n : Nat) :
    (((c.ends side).closed = false ∧ (c.stream (!side)).bytes = [] ∧
      (c.stream (!side)).status = .live)) ∨
    ∃ data code c₂, ReadOutcome c side n data code c₂ := by
  by_cases hc : (c.ends side).closed = true
  · right; exact ⟨[], errClosed, c, by simp [ReadOutcome, hc]⟩
  by_cases hn : n = 0
  · right; exact ⟨[], errNone, c, by simp [ReadOutcome, hc, hn]⟩
  have hc' : (c.ends side).closed = false := by simpa using hc
  cases hb : (c.stream (!side)).bytes with
  | cons b bs =>
    right
    refine ⟨[b], errNone, c.setStream (!side)
      { c.stream (!side) with bytes := (c.stream (!side)).bytes.drop 1 }, ?_⟩
    unfold ReadOutcome; dsimp only
    rw [if_neg hc, if_neg hn]
    exact .inr (.inl ⟨by simp, by simp; omega, by rw [hb]; exact ⟨bs, rfl⟩, rfl, rfl⟩)
  | nil =>
    cases hs : (c.stream (!side)).status with
    | live => left; exact ⟨hc', rfl, rfl⟩
    | fin =>
      right; refine ⟨[], errEOF, c, ?_⟩
      unfold ReadOutcome; dsimp only
      rw [if_neg hc, if_neg hn]
      exact .inr (.inr (.inl ⟨hb, hs, rfl, rfl, rfl⟩))
    | cut =>
      right; refine ⟨[], errBroken, c, ?_⟩
      unfold ReadOutcome; dsimp only
      rw [if_neg hc, if_neg hn]
      exact .inr (.inr (.inr ⟨hb, hs, rfl, .inl rfl, rfl⟩))

theorem write_progress (c : Conn) (side : Side) (data : List w8) :
    ∃ k code c₂, WriteOutcome c side data k code c₂ := by
  by_cases hc : (c.ends side).closed = true
  · exact ⟨0, errClosed, c, by simp [WriteOutcome, hc]⟩
  · refine ⟨data.length, errNone, c.writeAppend side (data.take data.length), ?_⟩
    rw [writeOutcome_iff, if_neg hc]
    exact ⟨Nat.le_refl _, .inl ⟨rfl, rfl, rfl⟩⟩

theorem close_progress (c : Conn) (side : Side) : ∃ code c₂, CloseOutcome c side code c₂ := by
  by_cases hc : (c.ends side).closed = true
  · exact ⟨errClosed, c, by simp [CloseOutcome, hc]⟩
  · refine ⟨errNone, (c.setEnd side { c.ends side with closed := true }).setStream side
      (if (c.stream side).status = .live then { c.stream side with status := .fin }
       else c.stream side), ?_⟩
    · unfold CloseOutcome; dsimp only
      rw [if_neg hc]
      exact ⟨rfl, rfl⟩

theorem deadline_progress (c : Conn) (side : Side) (which : w64) (set : Bool)
    (hw : which = 0 ∨ which = 1 ∨ which = 2) :
    ∃ code c₂, DeadlineOutcome c side which set code c₂ := by
  by_cases hc : (c.ends side).closed = true
  · exact ⟨errClosed, c, by simp [DeadlineOutcome, hc]⟩
  · refine ⟨errNone, ?_⟩
    unfold DeadlineOutcome; dsimp only
    simp only [if_neg hc, true_and]
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, .inr (.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, .inr (.inr ⟨rfl, rfl⟩)⟩

end progress

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The extension's ghost state in the program's. -/
abbrev netGS : NetConnGS GF := extGlobalGS netConnExt

/-- This node's IP (the extension's local state, `localCtx`). -/
abbrev netIp : GoString := (extLocalGS netConnExt (L := L) : NetConnNodeGS GF).ip

/-- This node's IP is `ip` (pure, so persistent): what a `Listen` on a wildcard host needs
(`wp_ListenWild`). The statement gives node `i` the fact for its configured IP
(`Harness.SafeDist`, `NodeBootWpAt`). -/
abbrev nodeIp (ip : GoString) : IProp GF := iprop(⌜netIp (L := L) (GF := GF) = ip⌝)

/-- Connection `cid` exists (persistent). -/
abbrev isConnP (cid : w64) : IProp GF := isConnG (netGS (G := G)) cid
/-- Listener `lid` was made by `Listen(a)` (persistent). -/
abbrev isListener (lid : w64) (a : GoString) : IProp GF := isListenerG (netGS (G := G)) lid a
/-- The writer's half of the stream written at end `side` of `cid`: `W` written, protocol `P`. -/
abbrev sendTok (cid : w64) (side : Side) (P : Proto GF) (W : List w8) : IProp GF :=
  sendTokG (netGS (G := G)) cid side P W
/-- The reader's half at end `side` of `cid`: `R` read, protocol `P` of the bytes it reads. -/
abbrev recvTok (cid : w64) (side : Side) (P : Proto GF) (R : List w8) : IProp GF :=
  recvTokG (netGS (G := G)) cid side P R
/-- End `side` of `cid` is new: handed out once, by the `Dial` or `Accept` that made it
(exclusive: `connFresh_excl`). -/
abbrev connFresh (cid : w64) (side : Side) : IProp GF := connFreshG (netGS (G := G)) cid side
/-- `bs` was written to the stream written at end `s` of `cid` (persistent). -/
abbrev sentLb (cid : w64) (s : Side) (bs : List w8) : IProp GF :=
  sentLbG (netGS (G := G)) cid s bs
/-- The token of the configured address `a`. -/
abbrev addrTok (a : GoString) : IProp GF := addrTokG (netGS (G := G)) a
/-- The protocols of the configured address `a`, not set yet. -/
abbrev addrUnset (a : GoString) : IProp GF := addrUnsetG (netGS (G := G)) a
/-- The protocols of the configured address `a`: `P` for what dialers write, `Q` for what
acceptors write (persistent). -/
abbrev addrProto (a : GoString) (P Q : Proto GF) : IProp GF := addrProtoG (netGS (G := G)) a P Q
/-- The end `side` of `cid`: writing with protocol `Pout` (written `W`), reading with protocol
`Pin` (read `R`). -/
abbrev connEnd (cid : w64) (side : Side) (Pout Pin : Proto GF) (W R : List w8) : IProp GF :=
  iprop(sendTok cid side Pout W ∗ recvTok cid side Pin R)
/-- A listener made by `Listen(a)`, and the address's token (given back by `Close`). -/
abbrev listening (lid : w64) (a : GoString) : IProp GF := iprop(isListener lid a ∗ addrTok a)

/-- An end is new at most once. -/
theorem connFresh_excl (cid : w64) (side : Side) :
    connFresh (G := G) cid side ∗ connFresh cid side ⊢ (False : IProp GF) :=
  connFreshG_excl _ cid side

/-- What a reader has read meets its protocol, up to extension (`protoPrefix`): the reader's
use of the protocol. -/
theorem recvTok_proto (cid : w64) (side : Side) (P : Proto GF) (R : List w8) :
    recvTok (G := G) cid side P R ⊢
      recvTok cid side P R ∗ protoPrefix (GF := GF) P cid R := by
  refine persistent_entails_left (Q := protoPrefix (GF := GF) P cid R) ?_
  unfold recvTok recvTokG recvTokN
  iintro ⟨%n, -, -, -, -, #Hp⟩
  iexact Hp

/-- The bytes written so far at end `side` (persistent, for the peer's progress arguments). -/
theorem sendTok_sentLb (cid : w64) (side : Side) (P : Proto GF) (W : List w8) :
    sendTok (G := G) cid side P W ⊢ sendTok cid side P W ∗ sentLb cid side W := by
  refine persistent_entails_left (Q := sentLb (G := G) cid side W) ?_
  unfold sendTok sendTokG sendTokN sentLb sentLbG
  iintro ⟨%n, #Hn, HW, -⟩
  ihave ⟨-, #Hlb⟩ := wHalf_lb (netGS (G := G)) _ (W' := W) (List.prefix_refl W) $$ HW
  iexists n
  iframe Hn
  iexact Hlb

/-- The interpretation of the node's local state: it is the node's IP. -/
theorem localCtx_ip (σ : GoString) :
    netConn_interp.localCtx (extLocalGS netConnExt (L := L) (GF := GF)) σ ⊢
      ⌜σ = netIp (L := L)⌝ ∗ netConn_interp.localCtx (extLocalGS netConnExt (L := L)) σ := by
  show iprop(⌜σ = netIp (L := L) (GF := GF)⌝) ⊢
    iprop(⌜σ = netIp (L := L) (GF := GF)⌝ ∗ ⌜σ = netIp (L := L) (GF := GF)⌝)
  iintro %h
  isplitr <;> ipureintro <;> exact h

/-- The core lifting lemma: a step of the extension, given that one exists (`Hprog`); the
operation's waiting steps (which change nothing) are handled here, by Löb induction. -/
theorem wp_netOp (op : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (Hstut : ∀ g g', NetConnStep (netIp (L := L)) op v g
      (ExternalOp netConnExt.name op (Val v)) g' → g' = g) :
    ⊢ □ (∀ g, netCtx (netGS (G := G)) g -∗
        ⌜∃ e' g', NetConnStep (netIp (L := L)) op v g e' g'⌝ ∗ netCtx (netGS (G := G)) g) -∗
      ▷ (∀ g e' g', ⌜NetConnStep (netIp (L := L)) op v g e' g'⌝ -∗
        ⌜e' ≠ ExternalOp netConnExt.name op (Val v)⌝ -∗
        netCtx (netGS (G := G)) g -∗ £ 1 ={E}=∗
          netCtx (netGS (G := G)) g' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp netConnExt.name op (Val v)) @ s; E {{ Φ }} := by
  iintro #Hprog
  iloeb as IH
  iintro Hcont
  iapply wp_extStep (X := netConnExt) op v Φ hv
  iintro %h %σ %g Hheap Hl Hg
  ihave ⟨%Hσ, Hl⟩ := localCtx_ip σ $$ Hl
  subst Hσ
  ihave ⟨%Hred, Hg⟩ := Hprog $$ %g Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    obtain ⟨e', g', Hs⟩ := Hred
    exact ⟨e', h, _, g', ⟨rfl, rfl, Hs⟩⟩
  inext
  iintro %e' %h' %σ' %g' %Hst Hcred
  obtain ⟨rfl, rfl, Hs⟩ := Hst
  imod Hclose
  by_cases hst : e' = ExternalOp netConnExt.name op (Val v)
  · subst hst
    obtain rfl := Hstut g g' Hs
    imodintro
    iframe Hheap Hl Hg
    iapply IH
    inext
    iexact Hcont
  · imod Hcont $$ %g %e' %g' %Hs %hst Hg Hcred with ⟨Hg, Hwp⟩
    imodintro
    iframe

/-- `Close` of end `side` of `cid`: any result; no ghost state changes. -/
theorem wp_Close (cid : w64) (side : Bool) :
    {{ isConnP (G := G) cid }}
      (ExternalOp netConnExt.name "Close" (Val (PairV #cid #side))) @ s; E
    {{ (code : w64), RET #code; True }} := by
  iintro %Φ #Hc HΦ
  unfold isConnP isConnG
  icases Hc with ⟨%n, #Hn⟩
  iapply wp_netOp "Close" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  · imodintro
    iintro %g Hg
    ihave ⟨%Hex, Hg⟩ := netCtx_conn netGS g cid n $$ Hg Hn
    iframe Hg
    ipureintro
    obtain ⟨c, hc⟩ := Hex
    obtain ⟨code, c₂, hco⟩ := close_progress c side
    exact ⟨_, _, cid, side, c, rfl, hc, c, c₂, code, .inl rfl, hco, rfl, rfl⟩
  · inext
    iintro %g %e' %g' %Hs %_ Hg _
    simp only [NetConnStep] at Hs
    obtain ⟨cid', side', c, hv, hc, c₁, c₂, code, hb, hco, rfl, rfl⟩ := Hs
    obtain ⟨h1, h2⟩ := val.PairV.inj hv
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    ihave ⟨%c0, %hc0, Hci, Hclose⟩ := netCtx_conn_acc netGS g cid n $$ Hg Hn
    rw [hc] at hc0
    obtain rfl := Option.some.inj hc0
    ihave Hci := connInvN_mono netGS cid n (breakOrNot_rel hb) $$ Hci
    ihave Hci := connInvN_mono netGS cid n (close_rel hco) $$ Hci
    ihave Hg := Hclose $$ %c₂ Hci
    imodintro
    iframe Hg
    iapply wp_value'
    iapply HΦ $$ %code
    itrivial

/-- `SetDeadline` (`which` 0), `SetReadDeadline` (1) or `SetWriteDeadline` (2) at end `side`:
any result; no ghost state changes. -/
theorem wp_SetDeadline (cid : w64) (side : Bool) (which : w64) (set : Bool)
    (hw : which = 0 ∨ which = 1 ∨ which = 2) :
    {{ isConnP (G := G) cid }}
      (ExternalOp netConnExt.name "SetDeadline"
        (Val (PairV #cid (PairV #side (PairV #which #set))))) @ s; E
    {{ (code : w64), RET #code; True }} := by
  iintro %Φ #Hc HΦ
  unfold isConnP isConnG
  icases Hc with ⟨%n, #Hn⟩
  iapply wp_netOp "SetDeadline" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := h
    cases h
  · imodintro
    iintro %g Hg
    ihave ⟨%Hex, Hg⟩ := netCtx_conn netGS g cid n $$ Hg Hn
    iframe Hg
    ipureintro
    obtain ⟨c, hc⟩ := Hex
    obtain ⟨code, c₂, hd⟩ := deadline_progress c side which set hw
    exact ⟨_, _, cid, side, which, set, c, rfl, hc, c₂, code, hd, rfl, rfl⟩
  · inext
    iintro %g %e' %g' %Hs %_ Hg _
    simp only [NetConnStep] at Hs
    obtain ⟨cid', side', which', set', c, hv, hc, c₂, code, hd, rfl, rfl⟩ := Hs
    obtain ⟨h1, h2⟩ := val.PairV.inj hv
    obtain ⟨h2, h3⟩ := val.PairV.inj h2
    obtain ⟨h3, h4⟩ := val.PairV.inj h3
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    obtain rfl := go.intoVal_inj h3
    obtain rfl := go.intoVal_inj h4
    ihave ⟨%c0, %hc0, Hci, Hclose⟩ := netCtx_conn_acc netGS g cid n $$ Hg Hn
    rw [hc] at hc0
    obtain rfl := Option.some.inj hc0
    ihave Hci := connInvN_mono netGS cid n (c' := c₂)
      (fun s W R h => by rw [deadline_stream hd]; exact h) $$ Hci
    ihave Hg := Hclose $$ %c₂ Hci
    imodintro
    iframe Hg
    iapply wp_value'
    iapply HΦ $$ %code
    itrivial

/-- `Write` of `data` at end `side`: appends `data.take k` to what the writer has written, `k`
being all of `data` when there is no error. The writer proves the protocol of the whole
`W ++ data`. -/
theorem wp_Write (cid : w64) (side : Bool) (data : List w8) (P : Proto GF) (W : List w8) :
    {{ sendTok (G := G) cid side P W ∗ □ P cid (W ++ data) }}
      (ExternalOp netConnExt.name "Write" (Val (PairV #cid (PairV #side #data)))) @ s; E
    {{ (k : Nat) (code : w64), RET PairV #(W64 k) #code;
       ⌜k ≤ data.length ∧ (code = errNone → k = data.length)⌝ ∗
       sendTok cid side P (W ++ data.take k) }} := by
  iintro %Φ ⟨Htok, #HPd⟩ HΦ
  unfold sendTok sendTokG
  icases Htok with ⟨%n, #Hn, Htok⟩
  iapply wp_netOp "Write" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  · imodintro
    iintro %g Hg
    ihave ⟨%Hex, Hg⟩ := netCtx_conn netGS g cid n $$ Hg Hn
    iframe Hg
    ipureintro
    obtain ⟨c, hc⟩ := Hex
    obtain ⟨k, code, c₂, hw⟩ := write_progress c side data
    exact ⟨_, _, cid, side, data, c, rfl, hc, c, c₂, k, code, .inl rfl, hw, rfl, rfl⟩
  · inext
    iintro %g %e' %g' %Hs %_ Hg _
    simp only [NetConnStep] at Hs
    obtain ⟨cid', side', data', c, hv, hc, c₁, c₂, k, code, hb, hw, rfl, rfl⟩ := Hs
    obtain ⟨h1, h2⟩ := val.PairV.inj hv
    obtain ⟨h2, h3⟩ := val.PairV.inj h2
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    obtain rfl := go.intoVal_inj (V := List w8) h3
    ihave ⟨%c0, %hc0, Hci, Hclose⟩ := netCtx_conn_acc netGS g cid n $$ Hg Hn
    rw [hc] at hc0
    obtain rfl := Option.some.inj hc0
    ihave Hci := connInvN_mono netGS cid n (breakOrNot_rel hb) $$ Hci
    imod connInvN_write netGS hw cid n P W $$ Hci Htok HPd with ⟨Hci, Htok⟩
    ihave Hg := Hclose $$ %c₂ Hci
    imodintro
    iframe Hg
    iapply wp_value'
    iapply HΦ $$ %k %code
    isplitr
    · ipureintro
      obtain ⟨-, -, h1, h2⟩ := write_rel hw
      exact ⟨h1, h2⟩
    · iexists n
      iframe Hn Htok


/-- `Listen(addr)` binding the configured address `a` (`listenAddr`), with `a`'s token: a new
listener on `a` (`listening lid a`, which keeps the token), or a failure (the token back). -/
theorem wp_Listen_at (addr a : GoString)
    (ha : a ∈ (netGS (G := G)).addrs → listenAddr (netIp (L := L)) addr = a) :
    {{ addrTok (G := G) a }}
      (ExternalOp netConnExt.name "Listen" (Val #addr)) @ s; E
    {{ (lid code : w64), RET PairV #lid #code;
       if code = errNone then listening lid a else addrTok a }} := by
  iintro %Φ Htok HΦ
  unfold addrTok addrTokG
  icases Htok with ⟨%hin, Ht⟩
  have hres := ha hin
  iapply wp_netOp "Listen" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, _, _, _, _, ⟨_, h⟩ | ⟨_, _, _, _, h⟩⟩ := h <;> cases h
  · imodintro
    iintro %g Hg
    ihave ⟨%Hadd, Hg⟩ := netCtx_addrs netGS g $$ Hg
    iframe Hg
    ipureintro
    exact ⟨_, _, addr, a, rfl, hres.symm, Hadd ▸ hin, .inl ⟨rfl, rfl⟩⟩
  · inext
    iintro %g %e' %g' %Hs %_ Hg _
    simp only [NetConnStep] at Hs
    obtain ⟨addr', a', hv, ha', -, ⟨rfl, rfl⟩ | ⟨lid, hfresh, -, rfl, rfl⟩⟩ := Hs
    · imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %(W64 0) %errFail
      simp only [show errFail ≠ errNone by decide, ite_false]
      iframe Ht
      ipureintro; exact hin
    · obtain rfl := go.intoVal_inj hv
      rw [hres] at ha'
      subst a'
      imod netCtx_listen netGS g lid a hfresh $$ Hg with ⟨Hg, #Hl⟩
      imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %lid %errNone
      simp only [ite_true]
      isplitr [Ht]
      · iexact Hl
      unfold addrTok addrTokG
      iframe Ht
      ipureintro; exact hin

/-- `Listen(a)`, with the address's token: a new listener (`listening lid a`, which keeps the
token), or a failure (the token back). (A configured address has no wildcard host, so it is
bound as spelled: `NetConnGS.addrs_tame`.) -/
theorem wp_Listen (a : GoString) :
    {{ addrTok (G := G) a }}
      (ExternalOp netConnExt.name "Listen" (Val #a)) @ s; E
    {{ (lid code : w64), RET PairV #lid #code;
       if code = errNone then listening lid a else addrTok a }} :=
  wp_Listen_at a a (fun hin => listenAddr_tame _ _ ((netGS (G := G)).addrs_tame a hin))

/-- `Listen(h ++ ":" ++ port)` on a wildcard host `h` (`":port"`, `"0.0.0.0:port"`,
`"[::]:port"`) at the node whose IP is `ip`: as `Listen(ip ++ ":" ++ port)`, with that address's
token [netsem: NodeIdentity]. -/
theorem wp_ListenWild (ip h port : GoString) (hh : h ∈ wildcardHosts) :
    {{ nodeIp (L := L) (GF := GF) ip ∗ addrTok (G := G) (ip ++ go!":" ++ port) }}
      (ExternalOp netConnExt.name "Listen" (Val #(h ++ go!":" ++ port))) @ s; E
    {{ (lid code : w64), RET PairV #lid #code;
       if code = errNone then listening lid (ip ++ go!":" ++ port)
       else addrTok (ip ++ go!":" ++ port) }} := by
  iintro %Φ ⟨%hip, Htok⟩ HΦ
  iapply wp_Listen_at (h ++ go!":" ++ port) (ip ++ go!":" ++ port)
    (fun _ => by rw [listenAddr_wild _ h port hh, hip]) $$ Htok HΦ

/-- `Close` of listener `lid`: any result. (Its address's token, if held, is the caller's to
keep: `listening lid a` gives back `addrTok a` by framing.) -/
theorem wp_CloseListener (lid : w64) (a : GoString) :
    {{ isListener (G := G) lid a }}
      (ExternalOp netConnExt.name "CloseListener" (Val #lid)) @ s; E
    {{ (code : w64), RET #code; True }} := by
  iintro %Φ #Hl HΦ
  iapply wp_netOp "CloseListener" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, l, _, _, h⟩ := h
    split at h <;> obtain ⟨_, h⟩ := h <;> cases h
  · imodintro
    iintro %g Hg
    ihave ⟨%Hex, Hg, -⟩ := netCtx_listener netGS g lid a $$ Hg Hl
    iframe Hg
    ipureintro
    obtain ⟨l, hl, -⟩ := Hex
    by_cases ho : l.isOpen = true
    · exact ⟨_, _, lid, l, rfl, hl, by rw [if_pos ho]; exact ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, lid, l, rfl, hl, by rw [if_neg ho]; exact ⟨rfl, rfl⟩⟩
  · inext
    iintro %g %e' %g' %Hs %_ Hg _
    simp only [NetConnStep] at Hs
    obtain ⟨lid', l, hv, hl, Hs⟩ := Hs
    obtain rfl := go.intoVal_inj hv
    split at Hs
    · obtain ⟨rfl, rfl⟩ := Hs
      ihave Hg := netCtx_closeListener netGS g lid l hl $$ Hg
      imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %errNone
      itrivial
    · obtain ⟨rfl, rfl⟩ := Hs
      imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %errClosed
      itrivial

/-- `Dial(a)`, knowing the address's protocols: the dialer's end of a new connection, or a
failure. -/
theorem wp_Dial (a : GoString) (P Q : Proto GF) :
    {{ addrProto (G := G) a P Q }}
      (ExternalOp netConnExt.name "Dial" (Val #a)) @ s; E
    {{ (cid code : w64), RET PairV #cid #code;
       if code = errNone then connEnd cid false P Q [] [] ∗ connFresh cid false else True }} := by
  iintro %Φ #Hpr HΦ
  iapply wp_netOp "Dial" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, _, _, ⟨_, h⟩ | ⟨_, _, _, _, _, _, _, ⟨_, h⟩ | ⟨_, h⟩⟩⟩ := h <;> cases h
  · imodintro
    iintro %g Hg
    ihave ⟨%Hadd, Hg⟩ := netCtx_addrs netGS g $$ Hg
    iframe Hg
    unfold addrProto addrProtoG
    icases Hpr with ⟨%hin, -⟩
    ipureintro
    exact ⟨_, _, a, rfl, Hadd ▸ hin, .inl ⟨rfl, rfl⟩⟩
  · inext
    iintro %g %e' %g' %Hs %_ Hg _
    simp only [NetConnStep] at Hs
    obtain ⟨a', hv, -, ⟨rfl, rfl⟩ | ⟨lid, l, cid, hl, hopen, haddr, hfresh,
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩⟩ := Hs
    · imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %(W64 0) %errFail
      simp only [show errFail ≠ errNone by decide, ite_false]
      itrivial
    · obtain rfl := go.intoVal_inj hv
      imod netCtx_dial netGS g lid l cid a P Q Conn.fresh streamRel_fresh hl hopen haddr hfresh
        $$ Hg Hpr with ⟨Hg, Hs, Hr, Hf⟩
      imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %cid %errNone
      simp only [ite_true]
      unfold connEnd sendTok recvTok connFresh
      iframe
    · -- a failed dial that reached the listener: the dialer's end is dropped
      obtain rfl := go.intoVal_inj hv
      imod netCtx_dial netGS g lid l cid a P Q Conn.abandoned streamRel_abandoned hl hopen haddr
        hfresh $$ Hg Hpr with ⟨Hg, -, -, -⟩
      imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %(W64 0) %errFail
      simp only [show errFail ≠ errNone by decide, ite_false]
      itrivial

/-- `Accept` on listener `lid` made by `Listen(a)`: the acceptor's end of a connection dialed to
`a`, or an error (a failure, or the listener closed). -/
theorem wp_Accept (lid : w64) (a : GoString) (P Q : Proto GF) :
    {{ isListener (G := G) lid a ∗ addrProto a P Q }}
      (ExternalOp netConnExt.name "Accept" (Val #lid)) @ s; E
    {{ (cid code : w64), RET PairV #cid #code;
       if code = errNone then connEnd cid true Q P [] [] ∗ connFresh cid true else True }} := by
  iintro %Φ ⟨#Hl, #Hpr⟩ HΦ
  iapply wp_netOp "Accept" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, l, _, _, h⟩ := h
    split at h
    · rcases h with ⟨_, rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, h⟩
      · rfl
      · cases h
      · cases h
    · obtain ⟨_, h⟩ := h; cases h
  · imodintro
    iintro %g Hg
    ihave ⟨%Hex, Hg, -⟩ := netCtx_listener netGS g lid a $$ Hg Hl
    iframe Hg
    ipureintro
    obtain ⟨l, hl, -⟩ := Hex
    by_cases ho : l.isOpen = true
    · exact ⟨_, _, lid, l, rfl, hl, by rw [if_pos ho]; exact .inr (.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, _, lid, l, rfl, hl, by rw [if_neg ho]; exact ⟨rfl, rfl⟩⟩
  · inext
    iintro %g %e' %g' %Hs %Hne Hg _
    ihave ⟨%Hex, Hg, -⟩ := netCtx_listener netGS g lid a $$ Hg Hl
    simp only [NetConnStep] at Hs
    obtain ⟨lid', l, hv, hl, Hs⟩ := Hs
    obtain rfl := go.intoVal_inj hv
    obtain ⟨l', hl', haddr⟩ := Hex
    rw [hl] at hl'
    obtain rfl := Option.some.inj hl'
    split at Hs
    · rename_i hopen
      rcases Hs with ⟨-, -, he⟩ | ⟨rfl, rfl⟩ | ⟨cid, hcid, rfl, rfl⟩
      · exact absurd he Hne
      · imodintro
        iframe Hg
        iapply wp_value'
        iapply HΦ $$ %(W64 0) %errFail
        simp only [show errFail ≠ errNone by decide, ite_false]
        itrivial
      · imod netCtx_accept netGS g lid l cid a P Q hl hopen haddr hcid $$ Hg Hpr
          with ⟨Hg, Hs, Hr, Hf⟩
        imodintro
        iframe Hg
        iapply wp_value'
        iapply HΦ $$ %cid %errNone
        simp only [ite_true]
        unfold connEnd sendTok recvTok connFresh
        iframe
    · obtain ⟨rfl, rfl⟩ := Hs
      imodintro
      iframe Hg
      iapply wp_value'
      iapply HΦ $$ %(W64 0) %errClosed
      simp only [show errClosed ≠ errNone by decide, ite_false]
      itrivial

end lifting

/-! `Read` needs a later credit (to take the later off a saved predicate's agreement), so it is
stated for the program logic with credits, which is the one the adequacy theorems use. -/

section liftingLC
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `Read` of at most `m` bytes at end `side`: the next bytes `data` of the stream, which the
reader adds to what it has read, with the protocol of an extension of it (in `recvTok`). An
error (`io.EOF`, a timeout, a break, a closed end) comes with no bytes. -/
theorem wp_Read (cid : w64) (side : Bool) (m : w64) (P : Proto GF) (R : List w8) :
    {{ recvTok (G := G) cid side P R }}
      (ExternalOp netConnExt.name "Read" (Val (PairV #cid (PairV #side #m)))) @ s; E
    {{ (data : List w8) (code : w64), RET PairV #data #code;
       ⌜data.length ≤ m.toNat ∧ (code ≠ errNone → data = []) ∧
         (code = errNone → m.toNat ≠ 0 → data ≠ [])⌝ ∗
       recvTok cid side P (R ++ data) }} := by
  iintro %Φ Htok HΦ
  unfold recvTok recvTokG
  icases Htok with ⟨%n, #Hn, Htok⟩
  iapply wp_netOp "Read" _ Φ (by simp [val.isPanic])
  · intro g g' h
    simp only [NetConnStep] at h
    obtain ⟨_, _, _, _, _, _, ⟨rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, h⟩⟩ := h
    · rfl
  · imodintro
    iintro %g Hg
    ihave ⟨%Hex, Hg⟩ := netCtx_conn netGS g cid n $$ Hg Hn
    iframe Hg
    ipureintro
    obtain ⟨c, hc⟩ := Hex
    rcases read_progress c side m.toNat with ⟨h1, h2, h3⟩ | ⟨data, code, c₂, hr⟩
    · exact ⟨_, _, cid, side, m, c, rfl, hc, .inl ⟨rfl, rfl, h1, h2, h3⟩⟩
    · exact ⟨_, _, cid, side, m, c, rfl, hc,
        .inr ⟨c, c₂, data, code, .inl rfl, hr, rfl, rfl⟩⟩
  · inext
    iintro %g %e' %g' %Hs %Hne Hg Hcred
    simp only [NetConnStep] at Hs
    obtain ⟨cid', side', m', c, hv, hc, ⟨-, he, -⟩ | ⟨c₁, c₂, data, code, hb, hr, rfl, rfl⟩⟩ := Hs
    · obtain ⟨h1, h2⟩ := val.PairV.inj hv
      obtain ⟨h2, h3⟩ := val.PairV.inj h2
      obtain rfl := go.intoVal_inj h1
      obtain rfl := go.intoVal_inj h2
      obtain rfl := go.intoVal_inj h3
      exact absurd he Hne
    obtain ⟨h1, h2⟩ := val.PairV.inj hv
    obtain ⟨h2, h3⟩ := val.PairV.inj h2
    obtain rfl := go.intoVal_inj h1
    obtain rfl := go.intoVal_inj h2
    obtain rfl := go.intoVal_inj h3
    ihave ⟨%c0, %hc0, Hci, Hclose⟩ := netCtx_conn_acc netGS g cid n $$ Hg Hn
    rw [hc] at hc0
    obtain rfl := Option.some.inj hc0
    ihave Hci := connInvN_mono netGS cid n (breakOrNot_rel hb) $$ Hci
    imod connInvN_read netGS hr cid n P R $$ Hci Htok with ⟨Hci, Htok⟩
    imod @lc_fupd_elim_later GF G.gooseInvGS E _ $$ Hcred Htok with Htok
    ihave Hg := Hclose $$ %c₂ Hci
    imodintro
    iframe Hg
    iapply wp_value'
    iapply HΦ $$ %data %code
    isplitr
    · ipureintro
      obtain ⟨-, -, -, h1, h2, h3⟩ := read_rel hr
      exact ⟨h1, h2, h3⟩
    · iexists n
      iframe Hn Htok

end liftingLC

end NetConn

end Perennial
