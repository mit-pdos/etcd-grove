/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/StepExec.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The executor (`epaxos-exec.go`) as a free event `exec (q, i)`: the execution of one committed
instance, and the run loop's handling of the executor's result (`executeOverwrite`) and of the
replicas' `Executed` notices (`handleExecuted`, `incrementNumReplicasExecuted`).

**The execution event's guard** (`execGuard`) abstracts `executeCommands`' scan and Tarjan's search
(`strongconnect`, G4's `nodeArray.Less`; stage 1's `Replica/Tarjan.lean`, `Replica/ExecModel.lean`):
instance `n` is committed (status COMMITTED) and belongs to a component `L` that is
* a strongly connected component popped after the executed instances outside it (`X0`): `sccStep`
  (every member committed or executed, every dependency of a member in `X0` or in `L`, strongly
  connected, disjoint from `X0`);
* popped after a dependency-closed executed set (`XClosed (depR s) X0`: `X0` is a union of whole
  components executed earlier; this makes `L` unique: the component of `n`);
* executed in G4's order up to `n`: a member of `L` is executed iff its key is below `n`'s.
The executor holds the replica's lock over a whole component (it waits, releasing the lock, only
for missing or uncommitted dependencies, and for nil commands, which committed copies never have),
so a component's executions are consecutive in reality; the model lets other events interleave.

The guard is a `Prop` decided classically (`stepExec` is noncomputable).
-/
module

public import Dsverify.Proof.gryff.Model.StepBase
public import Dsverify.Proof.gryff.Replica.ExecModel

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

open Perennial.gryff.replica (Node sccStep keyLt XClosed boxList)

/-- The copy of instance `n` if it is committed or executed. -/
def committedCopy (s : RState) (n : Node) : Option Copy :=
  if 0 ≤ n.1 ∧ n.1 < 3 ∧ 0 ≤ n.2 ∧ n.2 < SLOTS then
    match s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) with
    | some c => if c.status = St.COMMITTED ∨ c.status = St.EXECUTED then some c else none
    | none => none
  else none

/-- Instance `n` is executed (status EXECUTED). -/
def executedB (s : RState) (n : Node) : Bool :=
  match committedCopy s n with
  | some c => c.status == St.EXECUTED
  | none => false

/-- `u` depends on `w`: `u` is committed and `w = (q, j)` with `0 ≤ j ≤ deps[q]`, `q < N`
(`strongconnect` visits `ExecedUpTo[q] + 1 .. Deps[q]`; the instances up to `ExecedUpTo[q]` are
executed). -/
def depR (s : RState) (u w : Node) : Prop :=
  ∃ c, committedCopy s u = some c ∧ 0 ≤ w.1 ∧ w.1 < 3 ∧ 0 ≤ w.2 ∧
    w.2 ≤ sint.Z (c.deps.at w.1.toNat)

/-- G4's sort key of a committed instance: `(Seq, Leader, Slot)` of its copy. -/
def keyAt (s : RState) (n : Node) : Int × Int × Int :=
  match committedCopy s n with
  | some c => (sint.Z c.seq, sint.Z c.leader, sint.Z c.slot)
  | none => (0, n.1, n.2)

/-- The executed instances (in the box order). -/
def executedList (s : RState) : List Node := boxList.filter (executedB s)

/-- The guard of the execution of instance `n` (see the module comment). -/
def execGuard (s : RState) (n : Node) : Prop :=
  ∃ L : List Node, n ∈ L ∧ (∀ u ∈ L, (committedCopy s u).isSome) ∧
    sccStep (depR s) ((executedList s).filter (fun w => w ∉ L)) L ∧
    XClosed (depR s) ((executedList s).filter (fun w => w ∉ L)) ∧
    ∀ u ∈ L, (executedB s u = true ↔ keyLt (keyAt s u) (keyAt s n))

open Classical in
/-- The execution of instance `(q, i)` (`strongconnect`'s loop body for `w`, lines 129-191): a
committed no-op executes nothing (G44); else the first command (only: G44's note) is applied as a
CAS to the newer of the instance's base and `PrevValTag[0]`, its result's tag is that tag with
`Rmwc + 1` (G1), `PrevValTag[0]` is set to it, and the result goes to the run loop
(`executeOverwriteChan`, a message to self); the copy's status becomes EXECUTED. -/
noncomputable def stepExec (s : RState) (q i : w32) : StepRes := do
  if !inBox q i then disabled
  let some c := s.inst q i | disabled
  if c.status ≠ St.COMMITTED then disabled
  if ¬ execGuard s (sint.Z q, sint.Z i) then disabled
  let mut s := s
  let mut outs : List Out := []
  match c.cmds with
  | [] => pure ()
  | c0 :: _ =>
    -- `pvt, ok := PrevValTag[Cmds[0].K]`; `if !ok || w.Base.T.GreaterThan(pvt.T)`
    let vt0 : ValTag := match s.prevValTag with
      | none => c.base
      | some pvt => if c.base.t.gt pvt.t then c.base else pvt
    let vt1 : ValTag := if c0.oldV = vt0.v then { vt0 with v := c0.v } else vt0
    let vt : ValTag := { vt1 with t := { vt1.t with rmwc := vt1.t.rmwc + 1 } }
    s := { s with prevValTag := some vt }
    let some o := sendTo s.id (.executeOverwrite { v := vt.v, t := vt.t, leader := c.leader,
                                                   slot := c.slot })
      | dead -- dead: `r.Id` is a replica id
    outs := [o]
  s := s.setInst q i { c with status := St.EXECUTED }
  return (s, outs)

/-- `handleExecuted(ex)` → `incrementNumReplicasExecuted(inst)`: once a majority (`N/2 + 1 = 2`)
executed the instance, the leader answers its first client proposal (`completeRMWWriter` on the
proposal's writer, the client's connection when it proposed; the reply's value is the proposal's
`OldValue`, G43 / H-AN-1: the leader's own copy's commands are not read). -/
def handleExecuted (s : RState) (m : ExecutedM) : StepRes := do
  if !inBox m.replica m.inst then dead -- dead: Executed names an instance of the instance space
  let some c := s.inst m.replica m.inst | return (s, [])
  let some lb := c.lb | return (s, [])
  let lb := { lb with numReplicasExecuted := lb.numReplicasExecuted + 1 }
  if !lb.repliedClient && sge lb.numReplicasExecuted 2 then
    let lb := { lb with repliedClient := true }
    let some p := lb.clientProposals.head?
      | dead -- dead (G43): the bookkeeping of an executed instance at its leader has proposals
    return (s.setInst m.replica m.inst { c with lb := some lb },
      [.ext (.rmwReply p.client p.cmdId 1)])
  return (s.setInst m.replica m.inst { c with lb := some lb }, [])

/-- `executeOverwrite(eo)` (`executeOverwriteChan`): `HandleOverwrite(K, V, T)`, then the
instance's leader learns it is executed here (directly if it is this replica). -/
def stepExecuteOverwrite (s : RState) (m : ExecuteOverwriteM) : StepRes := do
  let s := s.overwrite m.v m.t
  let ex : ExecutedM := { replica := m.leader, inst := m.slot }
  if m.leader = s.id then
    handleExecuted s ex
  else
    let some o := sendPeer s m.leader (.executed ex) | dead -- dead: the leader is a replica id
    return (s, [o])

end Perennial.gryff.model
