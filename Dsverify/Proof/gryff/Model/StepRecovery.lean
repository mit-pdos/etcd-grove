/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/StepRecovery.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

EPaxos recovery (`epaxosrmwhandler.go`): `startRecoveryForInstance` (the recovery trigger, a free
event), `handlePrepare`, `handlePrepareReply`. TryPreAccept is unreachable (see
`stepPrepareReply`).
-/
module

public import Dsverify.Proof.gryff.Model.StepEpaxos

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

/-- The recovery trigger `(q, i)` (`instancesToRecover` → `startRecoveryForInstance(q, i)`). Its
guard: `q` a row, `0 ≤ i < crtInstance[q]` (the executor asks only for such instances; the run
loop handles the request later, when `crtInstance[q]` can only be larger). -/
def stepRecover (s : RState) (q i : w32) : StepRes := do
  if !(rowOk q && sle 0 i && slt i (s.crt q)) then disabled
  if !inBox q i then dead -- dead: crtInstance[q] ≤ 2^21 (budget)
  if let some c := s.inst q i then
    if c.status = St.COMMITTED ∨ c.status = St.EXECUTED then
      return (s, []) -- fix (G21)
  if let some c := s.inst q i then
    if sge (c.ballot.sshiftRight 4) maxBallotHi then
      return (s, []) -- fix (G39)
  let c : Copy := match s.inst q i with
    | some c => c
    | none => { cmds := [], ballot := 0, status := St.NONE, seq := 0, deps := nildeps, base := vt0,
                lb := none, slot := i, leader := q, vbal := -1 }
  -- `inst.lb` is new bookkeeping, keeping only the client proposals (both branches of the code)
  let lb : LB :=
    { clientProposals := match c.lb with
        | some lb => lb.clientProposals
        | none => [],
      maxRecvBallot := -1, prepareOKs := 0, allEqual := false, preAcceptOKs := 0, acceptOKs := 0,
      nacks := 0, originalDeps := nildeps, committedDeps := [], recoveryInst := none,
      preparing := true, numReplicasExecuted := 0, repliedClient := false }
  let ri : Option RecoveryInstance :=
    if c.status = St.ACCEPTED then
      some { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps, base := c.base,
             preAcceptCount := 0, leaderResponded := false, vbal := c.vbal }
    else if sge c.status St.PREACCEPTED then
      -- fix (G24)
      let count : w64 :=
        if c.status = St.PREACCEPTED_EQ ∧ c.vbal = 0 ∧ s.id ≠ q then 1 else 0
      some { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps, base := c.base,
             preAcceptCount := count, leaderResponded := (s.id == q), vbal := c.vbal }
    else none
  let c := { c with lb := some { lb with recoveryInst := ri },
                    ballot := makeBallotLargerThan s.id c.ballot }
  let s := s.setInst q i c
  let some outs := bcastPrepare s q i c.ballot | dead -- dead: peers
  return (s, outs)

/-- `handlePrepare(prepare)`. -/
def stepPrepare (s : RState) (m : PrepareM) : StepRes := do
  if !inBox m.replica m.inst then dead -- dead: Prepares are for instances of the instance space
  match s.inst m.replica m.inst with
  | none =>
    let s := s.setInst m.replica m.inst
      { cmds := [], ballot := m.ballot, status := St.NONE, seq := 0, deps := nildeps, base := vt0,
        lb := none, slot := m.inst, leader := m.replica, vbal := -1 }
    let r : PrepareReplyM :=
      { acceptorId := s.id, replica := m.replica, inst := m.inst, ok := TRUE, ballot := m.ballot,
        vbal := -1, status := St.NONE, cmds := [], seq := -1, deps := nildeps, base := vt0 }
    let some o := sendPeer s m.leaderId (.prepareReply r) | dead -- dead: Prepares come from peers
    return (s, [o])
  | some c =>
    let (ok, c) := if slt m.ballot c.ballot then (FALSE, c) else (TRUE, { c with ballot := m.ballot })
    let s := s.setInst m.replica m.inst c
    let r : PrepareReplyM :=
      { acceptorId := s.id, replica := m.replica, inst := m.inst, ok, ballot := c.ballot,
        vbal := c.vbal, status := c.status, cmds := c.cmds, seq := c.seq, deps := c.deps,
        base := c.base }
    let some o := sendPeer s m.leaderId (.prepareReply r) | dead -- dead: Prepares come from peers
    return (s, [o])

/-- A recovery candidate from a reply's copy. -/
def riOf (m : PrepareReplyM) (count : w64) (leaderResponded : Bool) : RecoveryInstance :=
  { cmds := m.cmds, status := m.status, seq := m.seq, deps := m.deps, base := m.base,
    preAcceptCount := count, leaderResponded, vbal := m.vbal }

/-- `handlePrepareReply(preply)`. -/
def stepPrepareReply (s : RState) (m : PrepareReplyM) : StepRes := do
  if !cmdsOk m.cmds then never
  if !inBox m.replica m.inst then dead -- dead: a reply to this replica's Prepare
  let some c := s.inst m.replica m.inst
    | dead -- dead: a reply to this replica's Prepare, sent with its copy (startRecoveryForInstance)
  let some lb0 := c.lb | return (s, [])
  if !lb0.preparing then return (s, [])
  if c.status = St.COMMITTED ∨ c.status = St.EXECUTED then return (s, []) -- fix (G21)
  if m.ok = FALSE then
    return (s.setInst m.replica m.inst { c with lb := some { lb0 with nacks := lb0.nacks + 1 } }, [])
  if m.ballot ≠ c.ballot then return (s, []) -- fix (G17)
  let mut lb := { lb0 with prepareOKs := lb0.prepareOKs + 1 }
  if m.status = St.COMMITTED ∨ m.status = St.EXECUTED then
    -- fix (G22): the reply's command; the copy (and its bookkeeping) is replaced
    let s := s.setInst m.replica m.inst
      { cmds := m.cmds, ballot := c.ballot, status := St.COMMITTED, seq := m.seq, deps := m.deps,
        base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := c.ballot }
    let some outs := bcastCommit s m.replica m.inst m.cmds m.seq m.deps m.base | dead -- dead: peers
    return (s, outs)
  if m.status = St.ACCEPTED then
    let better : Bool := match lb.recoveryInst with
      | none => true
      | some ri => ri.status ≠ St.ACCEPTED || slt ri.vbal m.vbal
    if better then
      lb := { lb with recoveryInst := some (riOf m 0 false) }
  let below : Bool := match lb.recoveryInst with
    | none => true
    | some ri => slt ri.status St.ACCEPTED
  if (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧ below then
    -- fix (G24)
    let unchanged : Bool := m.status == St.PREACCEPTED_EQ && m.vbal == 0 && m.acceptorId != m.replica
    let count : w64 := if unchanged then 1 else 0
    match lb.recoveryInst with
    | none => lb := { lb with recoveryInst := some (riOf m count false) }
    | some ri =>
      if unchanged && sgt ri.preAcceptCount 0 then
        lb := { lb with recoveryInst := some { ri with preAcceptCount := ri.preAcceptCount + 1 } }
      else if unchanged then
        lb := { lb with recoveryInst := some (riOf m 1 ri.leaderResponded) }
    if m.acceptorId = m.replica then
      let some ri := lb.recoveryInst | dead -- dead: set just above
      lb := { lb with recoveryInst := some { ri with leaderResponded := true } }
      return (s.setInst m.replica m.inst { c with lb := some lb }, [])
  if slt lb.prepareOKs NHALF then
    return (s.setInst m.replica m.inst { c with lb := some lb }, [])
  match lb.recoveryInst with
  | some ir =>
    -- (`e.R.Thrifty` is false)
    if ir.status = St.ACCEPTED ∨
        (!ir.leaderResponded ∧ sge ir.preAcceptCount NHALF ∧ ir.status = St.PREACCEPTED_EQ) then
      let c' := { c with cmds := ir.cmds, seq := ir.seq, deps := ir.deps, base := ir.base,
                         status := St.ACCEPTED, vbal := c.ballot,
                         lb := some { lb with preparing := false } }
      let s := s.setInst m.replica m.inst c'
      let some outs := bcastAccept s m.replica m.inst c'.ballot c'.cmds c'.seq c'.deps c'.base
        | dead -- dead: peers
      return (s, outs)
    else if !ir.leaderResponded ∧ sge ir.preAcceptCount ((NHALF + 1) / 2) then
      -- dead: TryPreAccept (`(N/2+1)/2 = 1`): `preAcceptCount > 0` holds only for a candidate of
      -- status PREACCEPTED_EQ (set from an unchanged copy, own or a reply's, and kept by `++`; an
      -- ACCEPTED candidate has count 0), so this condition implies the Accept branch's (G24)
      dead
    else
      -- `inst.lb.preparing = false` on the bookkeeping that startPhase1 replaces
      let s := s.setInst m.replica m.inst { c with lb := some { lb with preparing := false } }
      startPhase1 s m.replica m.inst c.ballot lb.clientProposals ir.cmds
  | none =>
    -- a no-op: deps 0 but on the instance's row (`var noop_deps [DS]int32`)
    let noopDeps := nildeps.setAt m.replica.toNat (m.inst - 1)
    let c' : Copy :=
      { cmds := [], ballot := c.ballot, status := St.ACCEPTED, seq := 0, deps := noopDeps,
        base := vt0, lb := some { lb with preparing := false }, slot := m.inst,
        leader := m.replica, vbal := c.ballot }
    let s := s.setInst m.replica m.inst c'
    let some outs := bcastAccept s m.replica m.inst c.ballot [] 0 noopDeps vt0 | dead -- dead: peers
    return (s, outs)

end Perennial.gryff.model
