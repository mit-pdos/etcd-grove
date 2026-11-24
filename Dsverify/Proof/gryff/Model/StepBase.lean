/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/StepBase.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The model's step functions: common definitions (outputs, the partiality markers, sends, the
participant's overwrite, and the EPaxos helpers of `epaxosrmwhandler.go`: `updateCommitted`,
`updateConflicts`, `updateAttributes`, `mergeAttributes`, the `bcast*` functions).

A step is `RState → ... → StepRes` (`Except Fail (RState × List Out)`), its outputs in the order of
the code's sends (`SendMsg` to peers, sends to the replica's own channels, client replies). A step
that is not `.ok` fails with one of (`Fail`):
* `never`: (a) an input the system never produces (another key, a dependency with key ≥ 0 where
  the kit sends none, a Write1 not forced, a command that is not a CAS on key 0);
* `disabled`: (b) a free event whose guard fails (client request budget, recovery trigger,
  execution);
* `dead`: (c) a branch where the Go code would panic (index outside the instance space, nil
  dereference, `SendMsg` to self); each is marked `-- dead: <why the protocol never gets here>`,
  to be refuted by the protocol's totality theorem.

The helpers whose only failures are `dead` (`advanceCut`, `updateCommitted`, `updateAttributes`,
`shortCircuit`, the sends) stay `Option`-valued (their callers turn `none` into `dead`); the markers
are overloaded (`FailM`) so that both read the same. `gStep` (the `kahn.Net`'s step) is
`StepRes.toOption ∘ stepR` (`Step.lean`): the three failures are `none` there.
-/
module

public import Dsverify.Proof.gryff.Model.Msg
public import Dsverify.Proof.gryff.Kahn.Defs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

/-- A replica's output: a message to a replica (itself included) or a reply to a client. -/
abbrev Out := kahn.Out 3 Msg Ext

/-- Why a step has no result. -/
inductive Fail where
  /-- (a) an input the system never produces -/
  | never
  /-- (b) a free event whose guard fails -/
  | disabled
  /-- (c) a branch where the Go code would panic -/
  | dead
deriving DecidableEq, Repr

/-- A step's result: `.ok (s', outs)`, or `.error f` with the reason `f`. -/
abbrev StepRes := Except Fail (RState × List Out)

/-- The result as an `Option` (every failure is `none`), the `kahn.Net`'s step. -/
abbrev StepRes.toOption (r : StepRes) : Option (RState × List Out) := Except.toOption r

/-- The monads the markers live in: `Except Fail` (the steps) and `Option` (helpers whose failures
are all `dead`, turned into `dead` by their callers). -/
class FailM (m : Type → Type) where
  failNever : {α : Type} → m α
  failDisabled : {α : Type} → m α
  failDead : {α : Type} → m α

instance : FailM (Except Fail) := ⟨.error .never, .error .disabled, .error .dead⟩
instance : FailM Option := ⟨none, none, none⟩

/-- (a) An input the system never produces. -/
abbrev never {m : Type → Type} [FailM m] {α : Type} : m α := FailM.failNever
/-- (b) A free event whose guard fails. -/
abbrev disabled {m : Type → Type} [FailM m] {α : Type} : m α := FailM.failDisabled
/-- (c) A branch where the Go code would panic (each use says why the protocol never gets there). -/
abbrev dead {m : Type → Type} [FailM m] {α : Type} : m α := FailM.failDead

/-! ## Sends -/

/-- A replica id as a process (`none`: not a replica id). -/
def dstOf (x : w32) : Option (Fin 3) :=
  if h : 0 ≤ sint.Z x ∧ sint.Z x < 3 then some ⟨(sint.Z x).toNat, by omega⟩ else none

/-- A message to replica `q` that goes to the own channel when `q == r.Id` (`replyRead1Replica`,
`sendWrite1To`, ...: both are a message to `q`). `none`: `q` is not a replica id (`SendMsg` would
index `PeerWriters` out of range). -/
def sendTo (q : w32) (m : Msg) : Option Out := (dstOf q).map (fun d => .send d m)

/-- `SendMsg(q, ...)` (`q` must be a peer: `PeerWriters[r.Id]` is nil, `SendMsg` to self would
dereference it). -/
def sendPeer (s : RState) (q : w32) (m : Msg) : Option Out :=
  if q = s.id then none else sendTo q m

/-- `e.R.PreferredPeerOrder[0..N-2]` (`NewReplicaDurable`: `(Id + 1 + i) % N`; never changed:
beacons are off). `e.R.Alive[q]` is true for every peer once `ConnectToPeers` returned (before the
run loop starts). -/
def peerOrder (s : RState) : List w32 :=
  [0, 1].map (fun i : Nat => BitVec.ofNat 32 ((s.id.toNat + 1 + i) % 3))

/-- A broadcast to the peers in `PreferredPeerOrder` (`bcastPreAccept`, `bcastAccept`,
`bcastCommit` with Exec: N - 1 = 2 sends, all peers alive). -/
def bcast (s : RState) (m : Msg) : Option (List Out) := (peerOrder s).mapM (fun q => sendPeer s q m)

/-! ## The participant's store (`GryffParticipant.HandleOverwrite`, key 0, noConflicts false) -/

/-- `HandleOverwrite(0, v, t)`: overwrite if the stored tag is less than `t`. -/
def RState.overwrite (s : RState) (v : w64) (t : Tag) : RState :=
  if s.tag.lt t then { s with val := v, tag := t } else s

/-! ## EPaxos helpers -/

/-- `e.R.N / 2` (Go `int`). -/
def NHALF : w64 := 1
/-- `fastPathQuorum()`: `2 * F`, `F = N / 2` (not thrifty). -/
def FPQ : w64 := 2

/-- The loop of `updateCommitted(q)` from `CommittedUpTo[q] = k`: the last `k'` such that
`k+1 .. k'` are committed or executed. Fuel: the loop ends at the first slot not committed, at most
`2^21 + 1` iterations (the box check comes first). -/
def advanceCut (s : RState) (q : w32) : Nat → w32 → Option w32
  | 0, _ => dead -- dead: the fuel exceeds the slots: the box check below stops the loop first
  | f + 1, k =>
    let j := k + 1
    if !inBox q j then
      dead -- dead: slot 2^21 is reached only if all 2^21 slots of row q are committed (budget)
    else
      match s.inst q j with
      | some c => if c.status = St.COMMITTED ∨ c.status = St.EXECUTED then advanceCut s q f j
                  else some k
      | none => some k

/-- `updateCommitted(replica)` (`replica` a valid row). -/
def updateCommitted (s : RState) (q : w32) : Option RState := do
  let some k := advanceCut s q (SLOTS.toNat + 1) (s.cut q)
    | dead -- dead: see `advanceCut`
  return { s with committedUpTo := s.committedUpTo.setAt q.toNat k }

/-- `updateConflicts(cmds, replica, instance, seq)` (noConflicts false; every command a CAS on
key 0, conflicting with every op type: all three per-op entries get the same value). -/
def updateConflicts (s : RState) (cmds : List Cmd) (replica islot seq : w32) : RState :=
  Id.run do
    let mut s := s
    for _c in cmds do
      let d : w32 := match s.confAt replica.toNat with
        | some hi => if slt hi islot then islot else hi
        | none => islot
      let m : w32 := match s.maxSeqK0 with
        | some ms => if slt ms seq then seq else ms
        | none => seq
      s := { s with conf := s.conf.set replica.toNat (some d), maxSeqK0 := some m }
    return s

/-- `updateAttributes(cmds, seq, deps, replica, instance)`: the new `(seq, deps, changed)`. -/
def updateAttributes (s : RState) (cmds : List Cmd) (seq0 : w32) (deps0 : Deps) (replica : w32) :
    Option (w32 × Deps × Bool) := do
  let mut seq := seq0
  let mut deps := deps0
  let mut changed := false
  for q in [0, 1, 2] do
    if s.id ≠ replica ∧ BitVec.ofNat 32 q = replica then continue
    for _c in cmds do
      match s.confAt q with
      | some hi =>
        if sgt hi (deps.at q) then
          deps := deps.setAt q hi
          let some w := (if inBox (BitVec.ofNat 32 q) hi then s.inst (BitVec.ofNat 32 q) hi else none)
            | dead -- dead: the conflict table records only instances this replica has a copy of
          if sle seq w.seq then
            seq := w.seq + 1
          changed := true
      | none => pure ()
  for _c in cmds do
    match s.maxSeqK0 with
    | some ms =>
      if sle seq ms then
        seq := ms + 1
        changed := true
    | none => pure ()
  return (seq, deps, changed)

/-- Go's `equal(&deps1, &deps2)`: the five entries agree. -/
def depsEqual (a b : Deps) : Bool := (List.range 5).all (fun q => a.at q == b.at q)

/-- `mergeAttributes(seq1, deps1, seq2, deps2)`: `(seq, deps, equal)`. -/
def mergeAttributes (s : RState) (seq1 : w32) (deps1 : Deps) (seq2 : w32) (deps2 : Deps) :
    w32 × Deps × Bool := Id.run do
  let mut equal := true
  let mut seq1 := seq1
  let mut deps1 := deps1
  if seq1 ≠ seq2 then
    equal := false
    if sgt seq2 seq1 then
      seq1 := seq2
  for q in [0, 1, 2] do
    if BitVec.ofNat 32 q = s.id then continue
    if deps1.at q ≠ deps2.at q then
      equal := false
      if sgt (deps2.at q) (deps1.at q) then
        deps1 := deps1.setAt q (deps2.at q)
  return (seq1, deps1, equal)

/-- `bcastPreAccept(replica, instance, ballot, cmds, seq, deps, base)`. -/
def bcastPreAccept (s : RState) (replica islot ballot : w32) (cmds : List Cmd) (seq : w32)
    (deps : Deps) (base : ValTag) : Option (List Out) :=
  bcast s (.preAccept { leaderId := s.id, replica, inst := islot, ballot, cmds, seq, deps, base })

/-- `bcastAccept(replica, instance, ballot, cmds, seq, deps, base)`. -/
def bcastAccept (s : RState) (replica islot ballot : w32) (cmds : List Cmd) (seq : w32)
    (deps : Deps) (base : ValTag) : Option (List Out) :=
  bcast s (.accept { leaderId := s.id, replica, inst := islot, ballot, seq, deps, cmds, base })

/-- `bcastCommit(replica, instance, cmds, seq, deps, base)` (Exec: an `ECommit` to every peer). -/
def bcastCommit (s : RState) (replica islot : w32) (cmds : List Cmd) (seq : w32) (deps : Deps)
    (base : ValTag) : Option (List Out) :=
  bcast s (.commit { replica, inst := islot, cmds, seq, deps, base })

/-- `bcastPrepare(replica, instance, ballot)`: its loop visits `(Id + 1) % N`, `(Id + 2) % N`, the
same peers in the same order as `PreferredPeerOrder`. -/
def bcastPrepare (s : RState) (replica islot ballot : w32) : Option (List Out) :=
  bcast s (.prepare { leaderId := s.id, replica, inst := islot, ballot })

end Perennial.gryff.model
