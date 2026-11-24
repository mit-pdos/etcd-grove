/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/StepEpaxos.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The EPaxos handlers of `epaxosrmwhandler.go` (phase 1, phase 2, commit): `HandleRMW`,
`handlePropose`, `startPhase1`, `handlePreAccept`, `handlePreAcceptReply`, `handlePreAcceptOK`,
`handleAccept`, `handleAcceptReply`, `handleCommit`, and the commit at the proposer that the last
three share (`leaderCommit`). Not modelled: `maxSeq` (written, never read but by checkpointing), the
stable store (not durable), statistics, checkpointing (`DO_CHECKPOINTING` is false).

Commands carried by messages are checked to be CAS on key 0 (`cmdsOk`, else `never`).
-/
module

public import Dsverify.Proof.gryff.Model.StepBase

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

/-- `startPhase1(replica, instance, ballot, proposals, cmds, batchSize)` (`batchSize` is read only
by checkpointing). -/
def startPhase1 (s : RState) (replica islot ballot : w32) (proposals : List Proposal)
    (cmds : List Cmd) : StepRes := do
  -- `var deps [DS]int32` then `deps[q] = -1` for q < N
  let mut deps0 : Deps := [-1, -1, -1, 0, 0]
  if replica ≠ s.id then
    deps0 := deps0.setAt replica.toNat (islot - 1) -- fix (G32)
  let some (seq, deps, _) := updateAttributes s cmds 0 deps0 replica
    | dead -- dead: see updateAttributes
  let some _c0 := cmds.head?
    | dead -- dead: `cmds[0]`: a batch has its first proposal; a restarted phase 1's command is
           -- a pre-accepted copy's, never empty (PreAccepts carry a batch)
  let base := s.storeVT -- `{GetCurrentValue(cmds[0].K), *GetStoreMetadata(cmds[0].K).Tag}`
  if !inBox replica islot then
    dead -- dead: a new instance's slot is below 2^21 (budget); a restarted one exists
  let lb : LB :=
    { clientProposals := proposals, maxRecvBallot := 0, prepareOKs := 0, allEqual := true,
      preAcceptOKs := 0, acceptOKs := 0, nacks := 0, originalDeps := deps,
      committedDeps := [-1, -1, -1, -1, -1], recoveryInst := none, preparing := false,
      numReplicasExecuted := 0, repliedClient := false }
  let c : Copy :=
    { cmds, ballot, status := St.PREACCEPTED, seq, deps, base, lb := some lb, slot := islot,
      leader := replica, vbal := ballot }
  let s := s.setInst replica islot c
  let s := updateConflicts s cmds replica islot seq
  let some outs := bcastPreAccept s replica islot ballot cmds seq deps base
    | dead -- dead: the peers are valid
  return (s, outs)

/-- Slot `(q, i)` holds a committed or executed copy (H2b-R2's guard in `handlePropose`). -/
def slotDecided (s : RState) (q i : w32) : Bool :=
  match s.inst q i with
  | some c => c.status == St.COMMITTED || c.status == St.EXECUTED
  | none => false

/-- `handlePropose(propose)`'s body after its guards: a batch of `len(ProposeChan) + 1`
proposals (at most `MAX_BATCH`), the later ones taken from `ProposeChan` (oldest first). -/
def handleProposeBody (s : RState) (p : Proposal) : StepRes := do
  let b : w64 := BitVec.ofNat 64 (s.proposeQ.length + 1)
  let batchSize : w64 := if sgt b MAX_BATCH then MAX_BATCH else b
  let instNo := s.crt s.id
  let s := s.setCrt s.id (instNo + 1)
  let taken := s.proposeQ.take (batchSize.toNat - 1)
  let s := { s with proposeQ := s.proposeQ.drop (batchSize.toNat - 1) }
  let proposals := p :: taken
  startPhase1 s s.id instNo 0 proposals (proposals.map Proposal.cmd)

/-- `handlePropose(propose)`: `handleProposeBody` behind two `dead` guards (H2b-R2, H2b-R3). -/
def handlePropose (s : RState) (p : Proposal) : StepRes := do
  if s.proposeQ.length + 1 ≥ 2 ^ 63 then
    dead -- dead (H2b-R3): `len(ProposeChan) + 1` overflows `int`; `ProposeChan` holds only
         -- re-proposals, bounded by the budget
  if slotDecided s s.id (s.crt s.id) then
    dead -- dead (H2b-R2): the new proposal's slot `(Id, crtInstance[Id])` holds a committed or
         -- executed copy; own-row copies at or above `crtInstance[Id]` are bare NONE copies
  handleProposeBody s p

/-- A successful `handlePropose` passed its guards and is its body. -/
theorem handlePropose_ok {s : RState} {p : Proposal} {r : RState × List Out}
    (h : handlePropose s p = .ok r) :
    s.proposeQ.length + 1 < 2 ^ 63 ∧ slotDecided s s.id (s.crt s.id) = false ∧
      handleProposeBody s p = .ok r := by
  unfold handlePropose at h
  by_cases h1 : s.proposeQ.length + 1 ≥ 2 ^ 63
  · simp [h1] at h; cases h
  simp only [h1, ite_false] at h
  by_cases h2 : slotDecided s s.id (s.crt s.id) = true
  · simp [h2] at h; cases h
  simp only [h2, Bool.false_eq_true, ite_false] at h
  exact ⟨by omega, by simpa using h2, h⟩

/-- The client's RMW (`rmwChan` → `HandleRMW`): a proposal of `Command{CAS, K, NewValue,
OldValue}`, command id `RequestId`, writer `GetClientWriter(ClientId)`. `D` is not read by
`HandleRMW`; the guard asks for the system's shape (key 0, no dependency: `D.Key < 0`, Go's own
test, a client id ≥ 0), the budget and a fresh (client id, request id) here (`RState.used`). -/
def stepClientRMW (s : RState) (rid cid : w32) (k : w64) (d : Dep) (oldV newV : w64) :
    StepRes := do
  if !(k == 0 && slt d.key 0 && sge cid 0) then never
  if s.nReqs ≥ 24 then disabled
  if (cid, rid) ∈ s.used then disabled -- ghost guard: a fresh (client id, request id) here
  let s := { s with nReqs := s.nReqs + 1, used := (cid, rid) :: s.used }
  handlePropose s { cmdId := rid, client := cid, cmd := { op := opCAS, k, v := newV, oldV } }

/-- `handlePreAccept(preAccept)`. -/
def stepPreAccept (s : RState) (m : PreAcceptM) : StepRes := do
  if !cmdsOk m.cmds then never
  if !inBox m.replica m.inst then
    dead -- dead: PreAccepts are for instances of the instance space
  let inst := s.inst m.replica m.inst
  if let some c := inst then
    if c.status = St.COMMITTED ∨ c.status = St.ACCEPTED ∨ c.status = St.EXECUTED then
      return (s, [])
  let mut s := s
  if sge m.inst (s.crt m.replica) then
    s := s.setCrt m.replica (m.inst + 1)
  let some (seq, deps, _) := updateAttributes s m.cmds m.seq m.deps m.replica
    | dead -- dead: see updateAttributes
  -- fix (G41): unchanged iff the attributes equal the PreAccept's
  let mut changed := seq != m.seq || !depsEqual deps m.deps
  let mut base := m.base
  let some _c0 := m.cmds.head?
    | dead -- dead: `preAccept.Command[0]`: a PreAccept carries a batch (startPhase1)
  if s.tag.gt base.t then
    base := s.storeVT
    changed := true
  let uncommittedDeps : Bool :=
    [0, 1, 2].any (fun q => sgt (deps.at q) (s.committedUpTo.at q))
  let status := if changed then St.PREACCEPTED else St.PREACCEPTED_EQ
  match inst with
  | some c =>
    if slt m.ballot c.ballot then
      let r : PreAcceptReplyM :=
        { replica := m.replica, inst := m.inst, ok := FALSE, ballot := c.ballot, seq := c.seq,
          deps := c.deps, base := c.base }
      let some o := sendPeer s m.leaderId (.preAcceptReply r)
        | dead -- dead: PreAccepts come from peers
      return (s, [o])
    else
      s := s.setInst m.replica m.inst
        { c with cmds := m.cmds, seq, deps, base, ballot := m.ballot, vbal := m.ballot, status }
  | none =>
    s := s.setInst m.replica m.inst
      { cmds := m.cmds, ballot := m.ballot, status, seq, deps, base, lb := none, slot := m.inst,
        leader := m.replica, vbal := m.ballot }
  s := updateConflicts s m.cmds m.replica m.inst m.seq
  if changed || uncommittedDeps || m.replica ≠ m.leaderId || !isInitialBallot m.ballot then
    let r : PreAcceptReplyM :=
      { replica := m.replica, inst := m.inst, ok := TRUE, ballot := m.ballot, seq, deps, base }
    let some o := sendPeer s m.leaderId (.preAcceptReply r)
      | dead -- dead: PreAccepts come from peers
    return (s, [o])
  else
    let some o := sendPeer s m.leaderId (.preAcceptOK { inst := m.inst })
      | dead -- dead: PreAccepts come from peers
    return (s, [o])

/-- The commit at the proposer of instance `(q, i)`, whose copy is `c` with bookkeeping `lb` (the
same code at `handlePreAcceptReply` 1409-1457, `handlePreAcceptOK` 1548-1594, `handleAcceptReply`
1719-1764): status COMMITTED, `updateCommitted(q)`, the client proposals re-proposed if the
committed value is not theirs (G11: fewer commands than proposals), `bcastCommit`. The "all clear"
loop replies to no client: every command is a CAS, so `NeedsWaitForExecute` holds (Dreply). -/
def leaderCommit (s : RState) (q i : w32) (c : Copy) (lb : LB) : StepRes := do
  let c := { c with status := St.COMMITTED, lb := some lb }
  let s := s.setInst q i c
  let some s := updateCommitted s q | dead -- dead: see updateCommitted
  let mut s := s
  let mut c := c
  if lb.clientProposals ≠ [] ∧ c.cmds.length < lb.clientProposals.length then
    s := { s with proposeQ := s.proposeQ ++ lb.clientProposals }
    c := { c with lb := none }
    s := s.setInst q i c
  let some outs := bcastCommit s q i c.cmds c.seq c.deps c.base | dead -- dead: peers
  return (s, outs)

/-- `handlePreAcceptReply(pareply)` (N = 3, not thrifty: `allCommitted` stays true). -/
def stepPreAcceptReply (s : RState) (m : PreAcceptReplyM) : StepRes := do
  if !inBox m.replica m.inst then dead -- dead: a reply to this replica's PreAccept
  let some c := s.inst m.replica m.inst
    | dead -- dead: a reply to this replica's PreAccept, sent with its copy (startPhase1)
  if c.status ≠ St.PREACCEPTED then return (s, [])
  if c.ballot ≠ m.ballot then return (s, [])
  let some lb := c.lb
    | dead -- dead: a copy pre-accepted at a ballot this replica proposed at has its bookkeeping
  if m.ok = FALSE then
    let lb := { lb with nacks := lb.nacks + 1,
                        maxRecvBallot := if sgt m.ballot lb.maxRecvBallot then m.ballot
                                         else lb.maxRecvBallot }
    -- `if inst.lb.nacks >= N/2 { // TODO }`
    return (s.setInst m.replica m.inst { c with lb := some lb }, [])
  let mut lb := { lb with preAcceptOKs := lb.preAcceptOKs + 1 }
  let (seq, deps, equal0) := mergeAttributes s c.seq c.deps m.seq m.deps
  let mut c := { c with seq, deps }
  let mut equal := equal0
  if m.base.t.gt c.base.t then
    c := { c with base := m.base }
    equal := false
  -- `(e.R.N <= 3 && !e.R.Thrifty)` holds
  lb := { lb with allEqual := lb.allEqual && equal }
  if sge lb.preAcceptOKs (FPQ - 1) && lb.allEqual && isInitialBallot c.ballot then
    leaderCommit s m.replica m.inst c lb
  else if sge lb.preAcceptOKs NHALF then
    let c' := { c with status := St.ACCEPTED, vbal := c.ballot, lb := some lb }
    let s := s.setInst m.replica m.inst c'
    let some outs := bcastAccept s m.replica m.inst c'.ballot c'.cmds c'.seq c'.deps c'.base
      | dead -- dead: peers
    return (s, outs)
  else
    return (s.setInst m.replica m.inst { c with lb := some lb }, [])

/-- `handlePreAcceptOK(pareply)`: for instance `(r.Id, Instance)`. -/
def stepPreAcceptOK (s : RState) (m : PreAcceptOKM) : StepRes := do
  if !inBox s.id m.inst then dead -- dead: a reply to this replica's PreAccept
  let some c := s.inst s.id m.inst
    | dead -- dead: a reply to this replica's own PreAccept, sent with its copy (startPhase1)
  if c.status ≠ St.PREACCEPTED then return (s, [])
  if !isInitialBallot c.ballot then return (s, [])
  let some lb := c.lb
    | dead -- dead: the leader's copy of its instance at ballot 0 has its bookkeeping
  let lb := { lb with preAcceptOKs := lb.preAcceptOKs + 1 }
  -- N = 3: `allCommitted` stays true
  if sge lb.preAcceptOKs (FPQ - 1) && lb.allEqual && isInitialBallot c.ballot then
    leaderCommit s s.id m.inst c lb
  else if sge lb.preAcceptOKs NHALF then
    let c := { c with status := St.ACCEPTED, vbal := c.ballot, lb := some lb }
    let s := s.setInst s.id m.inst c
    let some outs := bcastAccept s s.id m.inst c.ballot c.cmds c.seq c.deps c.base
      | dead -- dead: peers
    return (s, outs)
  else
    return (s.setInst s.id m.inst { c with lb := some lb }, [])

/-- `handleAccept(accept)` (no `updateConflicts` here, as in the code). -/
def stepAccept (s : RState) (m : EAcceptM) : StepRes := do
  if !cmdsOk m.cmds then never
  if !inBox m.replica m.inst then dead -- dead: Accepts are for instances of the instance space
  let inst := s.inst m.replica m.inst
  if let some c := inst then
    if c.status = St.COMMITTED ∨ c.status = St.EXECUTED then
      return (s, [])
  let mut s := s
  if sge m.inst (s.crt m.replica) then
    s := s.setCrt m.replica (m.inst + 1)
  match inst with
  | some c =>
    if slt m.ballot c.ballot then
      let r : AcceptReplyM := { replica := m.replica, inst := m.inst, ok := FALSE, ballot := c.ballot }
      let some o := sendPeer s m.leaderId (.acceptReply r) | dead -- dead: Accepts come from peers
      return (s, [o])
    s := s.setInst m.replica m.inst
      { c with status := St.ACCEPTED, ballot := m.ballot, vbal := m.ballot, cmds := m.cmds,
               seq := m.seq, deps := m.deps, base := m.base }
  | none =>
    s := s.setInst m.replica m.inst
      { cmds := m.cmds, ballot := m.ballot, status := St.ACCEPTED, seq := m.seq, deps := m.deps,
        base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := m.ballot }
  let r : AcceptReplyM := { replica := m.replica, inst := m.inst, ok := TRUE, ballot := m.ballot }
  let some o := sendPeer s m.leaderId (.acceptReply r) | dead -- dead: Accepts come from peers
  return (s, [o])

/-- `handleAcceptReply(areply)`. -/
def stepAcceptReply (s : RState) (m : AcceptReplyM) : StepRes := do
  if !inBox m.replica m.inst then dead -- dead: a reply to this replica's Accept
  let some c := s.inst m.replica m.inst
    | dead -- dead: a reply to this replica's Accept, sent with its copy
  if c.status ≠ St.ACCEPTED then return (s, [])
  if c.ballot ≠ m.ballot then return (s, [])
  let some lb := c.lb
    | dead -- dead: a copy accepted at a ballot this replica sent Accepts at has its bookkeeping
  if m.ok = FALSE then
    let lb := { lb with nacks := lb.nacks + 1,
                        maxRecvBallot := if sgt m.ballot lb.maxRecvBallot then m.ballot
                                         else lb.maxRecvBallot }
    return (s.setInst m.replica m.inst { c with lb := some lb }, [])
  let lb := { lb with acceptOKs := lb.acceptOKs + 1 }
  if sgt (lb.acceptOKs + 1) NHALF then
    leaderCommit s m.replica m.inst c lb
  else
    return (s.setInst m.replica m.inst { c with lb := some lb }, [])

/-- `handleCommit(commit)`. -/
def stepCommit (s : RState) (m : ECommitM) : StepRes := do
  if !cmdsOk m.cmds then never
  if !inBox m.replica m.inst then dead -- dead: Commits are for instances of the instance space
  let inst := s.inst m.replica m.inst
  let mut s := s
  if sge m.inst (s.crt m.replica) then
    s := s.setCrt m.replica (m.inst + 1)
  if let some c := inst then
    if c.status = St.EXECUTED then
      return (s, [])
  match inst with
  | some c =>
    let mut c := c
    if let some lb := c.lb then
      if lb.clientProposals ≠ [] ∧ m.cmds = [] then
        -- someone committed a no-op: propose them again
        s := { s with proposeQ := s.proposeQ ++ lb.clientProposals }
        c := { c with lb := none }
    c := { c with cmds := m.cmds, seq := m.seq, deps := m.deps, base := m.base,
                  status := St.COMMITTED }
    s := s.setInst m.replica m.inst c
  | none =>
    s := s.setInst m.replica m.inst
      { cmds := m.cmds, ballot := 0, status := St.COMMITTED, seq := m.seq, deps := m.deps,
        base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := 0 }
    s := updateConflicts s m.cmds m.replica m.inst m.seq
  let some s' := updateCommitted s m.replica | dead -- dead: see updateCommitted
  return (s', [])

end Perennial.gryff.model
