/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/Codec.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The events' encoding as prophecy words (D9, stage 2 plan §1, §5): `evCodec : kahn.Codec Ev`.

Each replica resolves its trace prophecy with `enc e` at each event `e` it takes (Go:
`etc/proph-patches/dsv-gryff/01-trace-prophecy.patch`, one resolution function per event kind, one `ResolveU64` per word, in this
order). `enc e` is a kind word, then the fields of the event's projection (`Msg.lean`: the fields
the model keeps; a dropped Go field is not resolved), in the structure's field order, each as a
`w64` the way Go's `uint64(x)` converts it (Perennial's `convert_*_to_uint64`):

* `w64` (`int64`, `state.Key`, `state.Value`): the word itself;
* `w32` (`int32`): `W64 (sint.Z x)` (sign-extended);
* `w8`: `W64 (uint.Z x)` for a `uint8` (`OK`, `state.Operation`), `W64 (sint.Z x)` for an `int8`
  (`PrepareReply.Status`);
* `Tag`: `Ts`, `Cid`, `Rmwc`; `ValTag`: `V`, then its tag; `Dep`: `Key`, then its `ValTag`;
  `Cmd`: `Op`, `K`, `V`, `OldValue`;
* a list (`[]state.Command`, and `Deps`, a Go `[5]int32` that the model keeps as a `List w32`):
  each element preceded by the word 1, then the word 0. A length prefix cannot satisfy `dec_enc`
  for every list (a list of length `2^64` would encode like the empty list), and the model's
  `Deps` has no length bound, so a list is self-delimiting; Go's `[5]int32` gives 11 words.

The kind words (1-24) follow `Msg`'s constructors, then `Ev`'s (`notes/stage2-codec.md`: the table
of kinds, Go resolution functions and words).

`dec1` is the inverse: a kind word, then the fields, each read back (`setWidth`). This file is the
codec's definition and its two computational facts, not a protocol proof.
-/
module

public import Dsverify.Proof.gryff.Model.Msg
public import Dsverify.Proof.gryff.Kahn.Defs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

namespace codec

/-! ## Words -/

/-- Go's `uint64(x)` of an `int32`. -/
def ofI32 (x : w32) : w64 := W64 (sint.Z x)
/-- Go's `uint64(x)` of an `int8`. -/
def ofI8 (x : w8) : w64 := W64 (sint.Z x)
/-- Go's `uint64(x)` of a `uint8`. -/
def ofU8 (x : w8) : w64 := W64 (uint.Z x)

/-- A decoder: reads a prefix of a word list, returns the rest. -/
abbrev Dec (α : Type) := StateT (List w64) Option α

/-- The failing decoder. -/
def fail {α : Type} : Dec α := fun _ => none

/-- One word. -/
def word : Dec w64 := fun l =>
  match l with
  | [] => none
  | x :: r => some (x, r)

def dI32 : Dec w32 := do let x ← word; pure (x.setWidth 32)
def dW8 : Dec w8 := do let x ← word; pure (x.setWidth 8)

@[simp] theorem word_run (x : w64) (r : List w64) : word.run (x :: r) = some (x, r) := rfl

@[simp] theorem dI32_run (x : w32) (r : List w64) : dI32.run (ofI32 x :: r) = some (x, r) := by
  have : (ofI32 x).setWidth 32 = x := by
    show (x.signExtend 64).setWidth 32 = x
    bv_decide
  simp [dI32, this]

@[simp] theorem dI8_run (x : w8) (r : List w64) : dW8.run (ofI8 x :: r) = some (x, r) := by
  have : (ofI8 x).setWidth 8 = x := by
    show (x.signExtend 64).setWidth 8 = x
    bv_decide
  simp [dW8, this]

@[simp] theorem dU8_run (x : w8) (r : List w64) : dW8.run (ofU8 x :: r) = some (x, r) := by
  have : (ofU8 x).setWidth 8 = x := by
    apply BitVec.eq_of_toNat_eq
    simp [ofU8]
  simp [dW8, this]

/-! ## Lists: each element after the word 1, then the word 0 -/

def encList {α : Type} (f : α → List w64) : List α → List w64
  | [] => [0]
  | a :: as => 1 :: (f a ++ encList f as)

/-- At most `n` markers. -/
def decListN {α : Type} (d : Dec α) : Nat → Dec (List α)
  | 0 => fail
  | n + 1 => do
    let m ← word
    if m = 0 then pure []
    else if m = 1 then do
      let a ← d
      let as ← decListN d n
      pure (a :: as)
    else fail

/-- A list (its markers are fewer than the input's words). -/
def decList {α : Type} (d : Dec α) : Dec (List α) := fun l => (decListN d l.length).run l

theorem encList_length {α : Type} (f : α → List w64) (as : List α) :
    as.length < (encList f as).length := by
  induction as with
  | nil => simp [encList]
  | cons a as ih => simp [encList]; omega

theorem decListN_enc {α : Type} (f : α → List w64) (d : Dec α)
    (hd : ∀ a r, d.run (f a ++ r) = some (a, r)) (as : List α) :
    ∀ n r, as.length < n → (decListN d n).run (encList f as ++ r) = some (as, r) := by
  induction as with
  | nil =>
    intro n r h
    cases n with
    | zero => omega
    | succ n => simp [decListN, encList]
  | cons a as ih =>
    intro n r h
    cases n with
    | zero => omega
    | succ n =>
      simp only [List.length_cons] at h
      simp [decListN, encList, hd, ih n r (by omega)]

theorem decList_enc {α : Type} (f : α → List w64) (d : Dec α)
    (hd : ∀ a r, d.run (f a ++ r) = some (a, r)) (as : List α) (r : List w64) :
    (decList d).run (encList f as ++ r) = some (as, r) := by
  show (decListN d _).run _ = _
  apply decListN_enc f d hd
  have := encList_length f as
  simp; omega

/-! ## Tags, values, dependencies, commands -/

def encTag (t : Tag) : List w64 := [ofI32 t.ts, ofI32 t.cid, ofI32 t.rmwc]
def decTag : Dec Tag := do
  let ts ← dI32; let cid ← dI32; let rmwc ← dI32
  pure ⟨ts, cid, rmwc⟩

def encVT (v : ValTag) : List w64 := v.v :: encTag v.t
def decVT : Dec ValTag := do
  let v ← word; let t ← decTag
  pure ⟨v, t⟩

def encDep (d : Dep) : List w64 := d.key :: encVT d.vt
def decDep : Dec Dep := do
  let key ← word; let vt ← decVT
  pure ⟨key, vt⟩

def encCmd (c : Cmd) : List w64 := [ofU8 c.op, c.k, c.v, c.oldV]
def decCmd : Dec Cmd := do
  let op ← dW8; let k ← word; let v ← word; let oldV ← word
  pure ⟨op, k, v, oldV⟩

def encCmds (cs : List Cmd) : List w64 := encList encCmd cs
def decCmds : Dec (List Cmd) := decList decCmd

def encDeps (d : Deps) : List w64 := encList (fun x => [ofI32 x]) d
def decDeps : Dec Deps := decList dI32

@[simp] theorem decTag_run (t : Tag) (r : List w64) : decTag.run (encTag t ++ r) = some (t, r) := by
  cases t; simp [decTag, encTag]

@[simp] theorem decVT_run (v : ValTag) (r : List w64) : decVT.run (encVT v ++ r) = some (v, r) := by
  cases v; simp [decVT, encVT]

@[simp] theorem decDep_run (d : Dep) (r : List w64) : decDep.run (encDep d ++ r) = some (d, r) := by
  cases d; simp [decDep, encDep]

@[simp] theorem decCmd_run (c : Cmd) (r : List w64) : decCmd.run (encCmd c ++ r) = some (c, r) := by
  cases c; simp [decCmd, encCmd]

@[simp] theorem decCmds_run (cs : List Cmd) (r : List w64) :
    decCmds.run (encCmds cs ++ r) = some (cs, r) :=
  decList_enc encCmd decCmd decCmd_run cs r

@[simp] theorem decDeps_run (d : Deps) (r : List w64) :
    decDeps.run (encDeps d ++ r) = some (d, r) :=
  decList_enc (fun x => [ofI32 x]) dI32 (fun a r => by simp) d r

/-! ## Messages (fields in the structure's order) -/

def encRead1 (m : Read1ProxiedM) : List w64 :=
  [ofI32 m.requestId, ofI32 m.clientId, m.k] ++ encDep m.d ++ [ofI32 m.replicaId] ++ encVT m.vt
def decRead1 : Dec Read1ProxiedM := do
  let requestId ← dI32; let clientId ← dI32; let k ← word; let d ← decDep
  let replicaId ← dI32; let vt ← decVT
  pure ⟨requestId, clientId, k, d, replicaId, vt⟩

def encRead2 (m : Read2ProxiedM) : List w64 :=
  [ofI32 m.requestId, ofI32 m.clientId, m.k] ++ encVT m.vt ++ [ofI32 m.replicaId]
def decRead2 : Dec Read2ProxiedM := do
  let requestId ← dI32; let clientId ← dI32; let k ← word; let vt ← decVT
  let replicaId ← dI32
  pure ⟨requestId, clientId, k, vt, replicaId⟩

def encRead1Reply (m : Read1ReplyM) : List w64 :=
  [ofI32 m.requestId, ofI32 m.clientId, ofI32 m.replicaId] ++ encVT m.vt
def decRead1Reply : Dec Read1ReplyM := do
  let requestId ← dI32; let clientId ← dI32; let replicaId ← dI32; let vt ← decVT
  pure ⟨requestId, clientId, replicaId, vt⟩

def encRead2Reply (m : Read2ReplyM) : List w64 := [ofI32 m.requestId, ofI32 m.clientId]
def decRead2Reply : Dec Read2ReplyM := do
  let requestId ← dI32; let clientId ← dI32
  pure ⟨requestId, clientId⟩

def encWrite1 (m : Write1ProxiedM) : List w64 :=
  [ofI32 m.requestId, ofI32 m.clientId, ofI32 m.forceWrite, m.k] ++ encDep m.d ++
    [ofI32 m.replicaId]
def decWrite1 : Dec Write1ProxiedM := do
  let requestId ← dI32; let clientId ← dI32; let forceWrite ← dI32; let k ← word
  let d ← decDep; let replicaId ← dI32
  pure ⟨requestId, clientId, forceWrite, k, d, replicaId⟩

def encWrite1Reply (m : Write1ReplyM) : List w64 :=
  [ofI32 m.requestId, ofI32 m.clientId] ++ encVT m.vt
def decWrite1Reply : Dec Write1ReplyM := do
  let requestId ← dI32; let clientId ← dI32; let vt ← decVT
  pure ⟨requestId, clientId, vt⟩

def encWrite2 (m : Write2ProxiedM) : List w64 :=
  [ofI32 m.requestId, ofI32 m.clientId, m.k] ++ encVT m.vt ++ [ofI32 m.replicaId]
def decWrite2 : Dec Write2ProxiedM := do
  let requestId ← dI32; let clientId ← dI32; let k ← word; let vt ← decVT
  let replicaId ← dI32
  pure ⟨requestId, clientId, k, vt, replicaId⟩

def encWrite2Reply (m : Write2ReplyM) : List w64 :=
  [ofI32 m.requestId, ofI32 m.clientId, ofI32 m.applied]
def decWrite2Reply : Dec Write2ReplyM := do
  let requestId ← dI32; let clientId ← dI32; let applied ← dI32
  pure ⟨requestId, clientId, applied⟩

def encPreAccept (m : PreAcceptM) : List w64 :=
  [ofI32 m.leaderId, ofI32 m.replica, ofI32 m.inst, ofI32 m.ballot] ++ encCmds m.cmds ++
    [ofI32 m.seq] ++ encDeps m.deps ++ encVT m.base
def decPreAccept : Dec PreAcceptM := do
  let leaderId ← dI32; let replica ← dI32; let inst ← dI32; let ballot ← dI32
  let cmds ← decCmds; let seq ← dI32; let deps ← decDeps; let base ← decVT
  pure ⟨leaderId, replica, inst, ballot, cmds, seq, deps, base⟩

def encPreAcceptReply (m : PreAcceptReplyM) : List w64 :=
  [ofI32 m.replica, ofI32 m.inst, ofU8 m.ok, ofI32 m.ballot, ofI32 m.seq] ++ encDeps m.deps ++
    encVT m.base
def decPreAcceptReply : Dec PreAcceptReplyM := do
  let replica ← dI32; let inst ← dI32; let ok ← dW8; let ballot ← dI32; let seq ← dI32
  let deps ← decDeps; let base ← decVT
  pure ⟨replica, inst, ok, ballot, seq, deps, base⟩

def encPreAcceptOK (m : PreAcceptOKM) : List w64 := [ofI32 m.inst]
def decPreAcceptOK : Dec PreAcceptOKM := do
  let inst ← dI32
  pure ⟨inst⟩

def encAccept (m : EAcceptM) : List w64 :=
  [ofI32 m.leaderId, ofI32 m.replica, ofI32 m.inst, ofI32 m.ballot, ofI32 m.seq] ++
    encDeps m.deps ++ encCmds m.cmds ++ encVT m.base
def decAccept : Dec EAcceptM := do
  let leaderId ← dI32; let replica ← dI32; let inst ← dI32; let ballot ← dI32; let seq ← dI32
  let deps ← decDeps; let cmds ← decCmds; let base ← decVT
  pure ⟨leaderId, replica, inst, ballot, seq, deps, cmds, base⟩

def encAcceptReply (m : AcceptReplyM) : List w64 :=
  [ofI32 m.replica, ofI32 m.inst, ofU8 m.ok, ofI32 m.ballot]
def decAcceptReply : Dec AcceptReplyM := do
  let replica ← dI32; let inst ← dI32; let ok ← dW8; let ballot ← dI32
  pure ⟨replica, inst, ok, ballot⟩

def encCommit (m : ECommitM) : List w64 :=
  [ofI32 m.replica, ofI32 m.inst] ++ encCmds m.cmds ++ [ofI32 m.seq] ++ encDeps m.deps ++
    encVT m.base
def decCommit : Dec ECommitM := do
  let replica ← dI32; let inst ← dI32; let cmds ← decCmds; let seq ← dI32
  let deps ← decDeps; let base ← decVT
  pure ⟨replica, inst, cmds, seq, deps, base⟩

def encPrepare (m : PrepareM) : List w64 :=
  [ofI32 m.leaderId, ofI32 m.replica, ofI32 m.inst, ofI32 m.ballot]
def decPrepare : Dec PrepareM := do
  let leaderId ← dI32; let replica ← dI32; let inst ← dI32; let ballot ← dI32
  pure ⟨leaderId, replica, inst, ballot⟩

def encPrepareReply (m : PrepareReplyM) : List w64 :=
  [ofI32 m.acceptorId, ofI32 m.replica, ofI32 m.inst, ofU8 m.ok, ofI32 m.ballot, ofI32 m.vbal,
    ofI8 m.status] ++ encCmds m.cmds ++ [ofI32 m.seq] ++ encDeps m.deps ++ encVT m.base
def decPrepareReply : Dec PrepareReplyM := do
  let acceptorId ← dI32; let replica ← dI32; let inst ← dI32; let ok ← dW8; let ballot ← dI32
  let vbal ← dI32; let status ← dW8; let cmds ← decCmds; let seq ← dI32; let deps ← decDeps
  let base ← decVT
  pure ⟨acceptorId, replica, inst, ok, ballot, vbal, status, cmds, seq, deps, base⟩

def encExecuted (m : ExecutedM) : List w64 := [ofI32 m.replica, ofI32 m.inst]
def decExecuted : Dec ExecutedM := do
  let replica ← dI32; let inst ← dI32
  pure ⟨replica, inst⟩

def encExecuteOverwrite (m : ExecuteOverwriteM) : List w64 :=
  [m.v] ++ encTag m.t ++ [ofI32 m.leader, ofI32 m.slot]
def decExecuteOverwrite : Dec ExecuteOverwriteM := do
  let v ← word; let t ← decTag; let leader ← dI32; let slot ← dI32
  pure ⟨v, t, leader, slot⟩

/-! ## Events -/

/-- An event's words: its kind (1-24), then its fields. -/
def encEv : Ev → List w64
  | .msg (.read1 m) => 1 :: encRead1 m
  | .msg (.read2 m) => 2 :: encRead2 m
  | .msg (.read1Reply m) => 3 :: encRead1Reply m
  | .msg (.read2Reply m) => 4 :: encRead2Reply m
  | .msg (.write1 m) => 5 :: encWrite1 m
  | .msg (.write2 m) => 6 :: encWrite2 m
  | .msg (.write1Reply m) => 7 :: encWrite1Reply m
  | .msg (.write2Reply m) => 8 :: encWrite2Reply m
  | .msg (.preAccept m) => 9 :: encPreAccept m
  | .msg (.preAcceptReply m) => 10 :: encPreAcceptReply m
  | .msg (.preAcceptOK m) => 11 :: encPreAcceptOK m
  | .msg (.accept m) => 12 :: encAccept m
  | .msg (.acceptReply m) => 13 :: encAcceptReply m
  | .msg (.commit m) => 14 :: encCommit m
  | .msg (.prepare m) => 15 :: encPrepare m
  | .msg (.prepareReply m) => 16 :: encPrepareReply m
  | .msg (.executed m) => 17 :: encExecuted m
  | .msg (.executeOverwrite m) => 18 :: encExecuteOverwrite m
  | .read rid cid k d => [19, ofI32 rid, ofI32 cid, k] ++ encDep d
  | .write rid cid k v d => [20, ofI32 rid, ofI32 cid, k, v] ++ encDep d
  | .rmw rid cid k d oldV newV => [21, ofI32 rid, ofI32 cid, k] ++ encDep d ++ [oldV, newV]
  | .forceWrite => [22]
  | .recover q i => [23, ofI32 q, ofI32 i]
  | .exec q i => [24, ofI32 q, ofI32 i]

/-- The event after its kind word `k`. -/
def decBody (k : w64) : Dec Ev :=
  match k.toNat with
  | 1 => do let m ← decRead1; pure (.msg (.read1 m))
  | 2 => do let m ← decRead2; pure (.msg (.read2 m))
  | 3 => do let m ← decRead1Reply; pure (.msg (.read1Reply m))
  | 4 => do let m ← decRead2Reply; pure (.msg (.read2Reply m))
  | 5 => do let m ← decWrite1; pure (.msg (.write1 m))
  | 6 => do let m ← decWrite2; pure (.msg (.write2 m))
  | 7 => do let m ← decWrite1Reply; pure (.msg (.write1Reply m))
  | 8 => do let m ← decWrite2Reply; pure (.msg (.write2Reply m))
  | 9 => do let m ← decPreAccept; pure (.msg (.preAccept m))
  | 10 => do let m ← decPreAcceptReply; pure (.msg (.preAcceptReply m))
  | 11 => do let m ← decPreAcceptOK; pure (.msg (.preAcceptOK m))
  | 12 => do let m ← decAccept; pure (.msg (.accept m))
  | 13 => do let m ← decAcceptReply; pure (.msg (.acceptReply m))
  | 14 => do let m ← decCommit; pure (.msg (.commit m))
  | 15 => do let m ← decPrepare; pure (.msg (.prepare m))
  | 16 => do let m ← decPrepareReply; pure (.msg (.prepareReply m))
  | 17 => do let m ← decExecuted; pure (.msg (.executed m))
  | 18 => do let m ← decExecuteOverwrite; pure (.msg (.executeOverwrite m))
  | 19 => do
    let rid ← dI32; let cid ← dI32; let k ← word; let d ← decDep
    pure (.read rid cid k d)
  | 20 => do
    let rid ← dI32; let cid ← dI32; let k ← word; let v ← word; let d ← decDep
    pure (.write rid cid k v d)
  | 21 => do
    let rid ← dI32; let cid ← dI32; let k ← word; let d ← decDep; let oldV ← word
    let newV ← word
    pure (.rmw rid cid k d oldV newV)
  | 22 => pure .forceWrite
  | 23 => do let q ← dI32; let i ← dI32; pure (.recover q i)
  | 24 => do let q ← dI32; let i ← dI32; pure (.exec q i)
  | _ => fail

/-- One event: its kind word, then its body. -/
def decEv (l : List w64) : Option (Ev × List w64) :=
  match l with
  | [] => none
  | k :: r => (decBody k).run r

/-! ## The facts -/

theorem decEv_enc (e : Ev) (rest : List w64) : decEv (encEv e ++ rest) = some (e, rest) := by
  cases e with
  | msg m =>
    cases m <;>
      simp [decEv, encEv, decBody, decRead1, encRead1, decRead2, encRead2, decRead1Reply,
        encRead1Reply, decRead2Reply, encRead2Reply, decWrite1, encWrite1, decWrite2, encWrite2,
        decWrite1Reply, encWrite1Reply, decWrite2Reply, encWrite2Reply, decPreAccept,
        encPreAccept, decPreAcceptReply, encPreAcceptReply, decPreAcceptOK, encPreAcceptOK,
        decAccept, encAccept, decAcceptReply, encAcceptReply, decCommit, encCommit, decPrepare,
        encPrepare, decPrepareReply, encPrepareReply, decExecuted, encExecuted,
        decExecuteOverwrite, encExecuteOverwrite]
  | _ => simp [decEv, encEv, decBody]

/-- A decoder that never lengthens its input. -/
structure Mono {α : Type} (d : Dec α) : Prop where
  le : ∀ l a r, d.run l = some (a, r) → r.length ≤ l.length

theorem mono_pure {α : Type} (a : α) : Mono (pure a : Dec α) := by
  constructor; intro l b r h; simp at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _

theorem mono_fail {α : Type} : Mono (fail : Dec α) := by
  constructor; intro l b r h; simp [StateT.run, fail] at h

theorem mono_bind {α β : Type} {x : Dec α} {f : α → Dec β} (hx : Mono x)
    (hf : ∀ a, Mono (f a)) : Mono (x >>= f) := by
  constructor; intro l b r h
  simp only [StateT.run_bind] at h
  cases hxl : x.run l with
  | none => simp [hxl] at h
  | some p =>
    obtain ⟨a, l'⟩ := p
    simp only [hxl, Option.bind_eq_bind, Option.bind_some] at h
    exact Nat.le_trans ((hf a).le l' b r h) (hx.le l a l' hxl)

theorem mono_word : Mono word := by
  constructor; intro l a r h
  cases l with
  | nil => simp [StateT.run, word] at h
  | cons x l => simp [StateT.run, word] at h; rw [← h.2]; simp

theorem mono_dI32 : Mono dI32 := mono_bind mono_word (fun _ => mono_pure _)
theorem mono_dW8 : Mono dW8 := mono_bind mono_word (fun _ => mono_pure _)

theorem mono_decListN {α : Type} {d : Dec α} (hd : Mono d) (n : Nat) : Mono (decListN d n) := by
  induction n with
  | zero => exact mono_fail
  | succ n ih =>
    refine mono_bind mono_word (fun m => ?_)
    by_cases h0 : m = 0
    · simp only [h0, ↓reduceIte]; exact mono_pure _
    · by_cases h1 : m = 1
      · simp only [h1, ↓reduceIte]
        exact mono_bind hd (fun a => mono_bind ih (fun _ => mono_pure _))
      · simp only [h0, h1, ↓reduceIte]; exact mono_fail

theorem mono_decList {α : Type} {d : Dec α} (hd : Mono d) : Mono (decList d) :=
  ⟨fun l => (mono_decListN hd l.length).le l⟩

theorem mono_decTag : Mono decTag :=
  mono_bind mono_dI32 fun _ => mono_bind mono_dI32 fun _ => mono_bind mono_dI32 fun _ => mono_pure _
theorem mono_decVT : Mono decVT :=
  mono_bind mono_word fun _ => mono_bind mono_decTag fun _ => mono_pure _
theorem mono_decDep : Mono decDep :=
  mono_bind mono_word fun _ => mono_bind mono_decVT fun _ => mono_pure _
theorem mono_decCmd : Mono decCmd :=
  mono_bind mono_dW8 fun _ => mono_bind mono_word fun _ => mono_bind mono_word fun _ =>
    mono_bind mono_word fun _ => mono_pure _
theorem mono_decCmds : Mono decCmds := mono_decList mono_decCmd
theorem mono_decDeps : Mono decDeps := mono_decList mono_dI32

/-- `Mono` of a `do` block over the decoders above. -/
macro "mono_tac" : tactic => `(tactic| repeat (first | with_reducible apply mono_pure | with_reducible apply mono_fail | with_reducible apply mono_word | with_reducible apply mono_dI32 | with_reducible apply mono_dW8 | with_reducible apply mono_decTag | with_reducible apply mono_decVT | with_reducible apply mono_decDep | with_reducible apply mono_decCmds | with_reducible apply mono_decDeps | with_reducible apply mono_bind | intro _))

theorem mono_decRead1 : Mono decRead1 := by unfold decRead1; mono_tac
theorem mono_decRead2 : Mono decRead2 := by unfold decRead2; mono_tac
theorem mono_decRead1Reply : Mono decRead1Reply := by unfold decRead1Reply; mono_tac
theorem mono_decRead2Reply : Mono decRead2Reply := by unfold decRead2Reply; mono_tac
theorem mono_decWrite1 : Mono decWrite1 := by unfold decWrite1; mono_tac
theorem mono_decWrite2 : Mono decWrite2 := by unfold decWrite2; mono_tac
theorem mono_decWrite1Reply : Mono decWrite1Reply := by unfold decWrite1Reply; mono_tac
theorem mono_decWrite2Reply : Mono decWrite2Reply := by unfold decWrite2Reply; mono_tac
theorem mono_decPreAccept : Mono decPreAccept := by unfold decPreAccept; mono_tac
theorem mono_decPreAcceptReply : Mono decPreAcceptReply := by unfold decPreAcceptReply; mono_tac
theorem mono_decPreAcceptOK : Mono decPreAcceptOK := by unfold decPreAcceptOK; mono_tac
theorem mono_decAccept : Mono decAccept := by unfold decAccept; mono_tac
theorem mono_decAcceptReply : Mono decAcceptReply := by unfold decAcceptReply; mono_tac
theorem mono_decCommit : Mono decCommit := by unfold decCommit; mono_tac
theorem mono_decPrepare : Mono decPrepare := by unfold decPrepare; mono_tac
theorem mono_decPrepareReply : Mono decPrepareReply := by unfold decPrepareReply; mono_tac
theorem mono_decExecuted : Mono decExecuted := by unfold decExecuted; mono_tac
theorem mono_decExecuteOverwrite : Mono decExecuteOverwrite := by unfold decExecuteOverwrite; mono_tac

theorem mono_decBody (k : w64) : Mono (decBody k) := by
  unfold decBody
  split
  all_goals first
    | exact mono_bind mono_decRead1 fun _ => mono_pure _
    | exact mono_bind mono_decRead2 fun _ => mono_pure _
    | exact mono_bind mono_decRead1Reply fun _ => mono_pure _
    | exact mono_bind mono_decRead2Reply fun _ => mono_pure _
    | exact mono_bind mono_decWrite1 fun _ => mono_pure _
    | exact mono_bind mono_decWrite2 fun _ => mono_pure _
    | exact mono_bind mono_decWrite1Reply fun _ => mono_pure _
    | exact mono_bind mono_decWrite2Reply fun _ => mono_pure _
    | exact mono_bind mono_decPreAccept fun _ => mono_pure _
    | exact mono_bind mono_decPreAcceptReply fun _ => mono_pure _
    | exact mono_bind mono_decPreAcceptOK fun _ => mono_pure _
    | exact mono_bind mono_decAccept fun _ => mono_pure _
    | exact mono_bind mono_decAcceptReply fun _ => mono_pure _
    | exact mono_bind mono_decCommit fun _ => mono_pure _
    | exact mono_bind mono_decPrepare fun _ => mono_pure _
    | exact mono_bind mono_decPrepareReply fun _ => mono_pure _
    | exact mono_bind mono_decExecuted fun _ => mono_pure _
    | exact mono_bind mono_decExecuteOverwrite fun _ => mono_pure _
    | mono_tac

theorem decEv_shorter (l : List w64) (e : Ev) (rest : List w64) (h : decEv l = some (e, rest)) :
    rest.length < l.length := by
  cases l with
  | nil => simp [decEv] at h
  | cons k r =>
    have := (mono_decBody k).le r e rest h
    simp; omega

end codec

/-- The events' codec: a replica resolves its prophecy with `evCodec.enc e` at each event `e`. -/
def evCodec : kahn.Codec Ev where
  enc := codec.encEv
  dec1 := codec.decEv
  dec_enc := codec.decEv_enc
  dec_shorter := codec.decEv_shorter

end Perennial.gryff.model
