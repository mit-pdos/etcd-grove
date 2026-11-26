/-
Lean-first (#33 S3c step 2, `notes/antithesis-rawnode-design.md` §2.2). **The per-input end
relations**: what one input does to a node's protocol state `PState`, as raft's code paths are, in
static mode with pre-vote and check-quorum off. They are raft's step function at the protocol level,
the content of `StepEnd` (`LemmasStepGates.lean`, the exact per-path end state over `NState`)
restated on `PState`; `InputEndLift.lean` lifts `StepEnd` to them through `toPState`. Pure: imports
only Protocol modules.

Their right-hand sides are `StepC`'s (`Protocol/StepC.lean`) rule by rule, but unlike `StepC*` they
admit no other composition: a term change only by the preamble (`PreEnd`) or a campaign
(`TickEnd`), messages only queued at the state after the preamble, a broadcast only of `MsgApp`s
(`AppSendOk`: `ReplOk` without its `SnapOk` disjunct, which the lifting lemmas exclude by a
hypothesis, `NoSnapSent`, until the snapshot exclusion of the design's §2.5 is settled).

Differences from the design's sketch (§2.2), each because the sketch's form is not what raft's
code or `StepEnd` says:
* a granted vote answers at the request's term `m.term` (Go's `Term: m.Term`, `vrespMsgOf`), not
  the node's: the two agree after the preamble, not for a term-0 request (`RecvEnd`'s first arm);
* `HandleEnd`'s undecided vote response says `¬ JLost` but not `¬ JQuorum` (`poll`'s spec pins the
  loss, `CandVoteRespResultC`, not the win);
* leader sends are `AppSendOk` (`AppOk` and `AppCommitEq`: Go's `Commit: r.raftLog.committed`, which
  `ReplSends` gives too), not `AppOk` alone;
* `WinEnd` takes no configuration (the quorum is `HandleEnd`'s); the commit test is `PCommitOk`
  (`StepC.commit`'s premises, `CommitOkC` of `raft__maybeCommit`'s spec);
* `ProposeEnd` takes the proposal message, not its entries: a forward is the message re-addressed
  (`StepC.propForward`), and a leader appends the conf-change loop's batch (`PropRepl`);
* `TickEnd`'s campaign has some request context `cl` (`HupGuard`'s; `[]` for a `MsgHup` in Go, which
  `hup`'s spec does not say).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.StepC
public import Proof.go_etcd_io.raft.v3.Protocol.StepR
public import Proof.go_etcd_io.raft.v3.Protocol.RnMode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open GMap go_etcd_io.raft.v3

section input_end
variable [GooseExts]

/-- What a leader's broadcast queues at `s` (`maybeSendAppend`'s `MsgApp`) at the configuration `c`:
`AppOk`, the commit index exactly the leader's (`AppCommitEq`, Go's `Commit: r.raftLog.committed`),
and (#33 S4, destinations) to a peer of the configuration (`c.ids`: `maybeSendAppend` sends only to a
peer of the progress map, whose ids are the configuration's, `ReplSends`). `ReplOk` without its
`MsgSnap` disjunct. -/
def AppSendOk (c : CfgM) (id : w64) (s : PState) (m : Msg) : Prop :=
  AppOk id s m ∧ AppCommitEq s m ∧ m.dst ∈ c.ids

/-- A step from `s` to `s'` queued no `MsgSnap`: whatever it appended to the outbox. The lifting
lemmas take it of the step (the design's §2.5: the RawNode layer discharges it at a node whose
storage is never compacted). -/
def NoSnapSent (s s' : PState) : Prop :=
  ∀ ms : List Msg, s'.outbox = s.outbox ++ ms → ∀ x ∈ ms, x.ty ≠ .snap

/-- `AppSendOk` reads only the term, the log and the commit index. -/
theorem AppSendOk.proper {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (Ht : s'.term = s.term)
    (Hb : s'.base = s.base) (Hl : s'.log = s.log) (Hc : s'.commit = s.commit)
    (H : AppSendOk c id s m) : AppSendOk c id s' m := by
  unfold AppSendOk AppOk AppCommitEq at *
  rw [Ht, Hb, Hl, Hc]; exact H

/-- `ReplOk` of a message that is no `MsgSnap` is `AppOk`. -/
theorem ReplOk.app {id : w64} {s : PState} {m : Msg} (H : ReplOk id s m) (Hn : m.ty ≠ .snap) :
    AppOk id s m :=
  H.elim (fun h => h) fun h => absurd h.1 Hn

/-- `NoSnapSent` reads only the outbox before the step. -/
theorem NoSnapSent.of_outbox {s s1 s' : PState} (Ho : s1.outbox = s.outbox)
    (H : NoSnapSent s s') : NoSnapSent s1 s' :=
  fun ms h => H ms (Ho ▸ h)

/-- **`Step`'s term preamble** (`raft.go:1063-1090`, `Step`'s `m.Term > r.Term` arm): a message of a
higher term makes the node a follower at that term (`becomeFollower(m.Term, lead)`, the sender
its leader for a leader's message: `MsgApp`, `MsgHeartbeat`, `MsgSnap`); one of the node's term
leaves it as it is. (A lower term is `RecvEnd`'s second arm.) -/
def PreEnd (_k : NodeK) (s : PState) (m : Msg) (s1 : PState) : Prop :=
  (uint.Z s.term < uint.Z m.term ∧
    s1 = pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0)) ∨
  (m.term = s.term ∧ s1 = s)

/-- **`handleAppendEntries`** (`raft.go:1792-1826`) at `s`, the node having adopted the sender as
leader (`padoptLeader`): exactly one of `StepC.appStale` (`m.Index < committed`: the reply carries
`committed`), `StepC.appAccept` (`maybeAppend`'s log, `commitTo(min(m.Commit, lastnewi))`, the
reply carries `lastnewi`) and `StepC.appReject` (the log does not match at `(m.LogTerm, m.Index)`:
the rejection with `findConflictByTerm`'s hint), as `HandleAppResult` states them. -/
def AppEnd (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (uint.Z m.index < uint.Z s.commit ∧
    s' = psendMsgs s [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []]) ∨
  (uint.Z s.commit ≤ uint.Z m.index ∧
    ∃ (lastnewi : w64) (es' : List EntryM),
      plogMaybeAppend s.base s.log (entryID.mk m.logterm m.index) m.entries
        = some (lastnewi, es') ∧
      s' = psendMsgs
        { s with
            log := es',
            commit := plogCommitTo s.commit
                        (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
        [Msg.mk .appResp id m.src s.term false lastnewi (W64 0) (W64 0) (W64 0) []]) ∨
  (uint.Z s.commit ≤ uint.Z m.index ∧
    ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) ∧
    ∃ (hint hintterm : w64),
      RejHintOk s.base s.log m.index m.logterm hint ∧ uint.Z hintterm ≤ uint.Z m.logterm ∧
      s' = psendMsgs s [Msg.mk .appResp id m.src s.term true m.index hintterm (W64 0) hint []])

/-- **A candidate's win** (`stepCandidate`'s `poll` won, `becomeLeader`, `bcastAppend`;
`raft.go:1680-1690`): the `Match` values `reset` left (`LeaderMatchOk`), the empty entry of the
term appended (`pwinState`), the self-acknowledgement queued (`pselfAck`), then the broadcast's
`MsgApp`s judged at the won state (`AppSendOk`). `StepC.win`'s right-hand side. -/
def WinEnd (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  ∃ (mt : GMap w64 w64) (ms : List Msg), LeaderMatchOk id s mt ∧
    (∀ x ∈ ms, AppSendOk c id (pwinState id s mt) x) ∧
    s' = psendMsgs (pwinState id s mt) ([pselfAck id (pwinState id s mt)] ++ ms)

/-- **`maybeCommit`'s commit** to `n` at the configuration `c` (`raft.go:740-749`): past the commit
index, inside the log, at an entry of the leader's term, acknowledged by a joint quorum
(`ackedBy`). `StepC.commit`'s premises; `CommitOkC` of `raft__maybeCommit`'s spec. -/
def PCommitOk (c : CfgM) (s : PState) (n : w64) : Prop :=
  uint.Z s.commit < uint.Z n ∧ uint.Z n ≤ plogLastIndexZ s.base s.log ∧
  plogTermAt s.base s.log n = some s.term ∧ JQuorum c (ackedBy s n)

/-- **A leader's appends at `s`** (`sendAppend`, `bcastAppend`, `maybeSendAppend`): `MsgApp`s
judged at `s` (`AppSendOk`). `StepC.sendApps` without snapshots. -/
def SendsEnd (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  ∃ ms : List Msg, (∀ x ∈ ms, AppSendOk c id s x) ∧ s' = psendMsgs s ms

/-- **`stepLeader`'s `MsgAppResp`** (`raft.go:1371-1565`) at `s`, the leader at the message's term:
an unknown sender (no `Progress`) changes nothing; a rejection keeps `Match` and may probe
(`SendsEnd`); an acknowledgement raises the sender's `Match` to `max Match m.Index`
(`MaybeUpdate`, `StepC.appResp`), then possibly commits (`PCommitOk` at the raised `Match` map,
`StepC.commit`), then appends (`SendsEnd` at the state after the commit). -/
def AppRespEnd (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (s.matched !! m.src = none ∧ s' = s) ∨
  (m.reject = true ∧ s.matched !! m.src ≠ none ∧ SendsEnd c id s s') ∨
  (m.reject = false ∧ ∃ (x n : w64), s.matched !! m.src = some x ∧
    (n = s.commit ∨
      PCommitOk c { s with matched :=
        <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched } n) ∧
    SendsEnd c id { s with
      matched := <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched,
      commit := n } s')

/-- **A proposal** (`MsgProp`, term `0`: `RawNode.Propose`'s or a forwarded one) at `s`: a leader
(`stepLeader`, `raft.go:1294-1340`) drops it (a transfer in progress, or `appendEntry` refusing the
batch) or appends the conf-change loop's batch (`PropRepl`) stamped at its term and index
(`StepC.propose`), queues the self-acknowledgement and broadcasts (`AppSendOk`); a follower with a
leader forwards it to the leader re-addressed, its term left `0` (`stepFollower`,
`StepC.propForward`); otherwise (a candidate, a follower with no leader) it is dropped. -/
def ProposeEnd (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  if s.role = .leader then
    s' = s ∨
    ∃ (es : List EntryM) (ms : List Msg), PropRepl m.entries es ∧
      (∀ x ∈ ms, AppSendOk c id (pappend s (es.mapIdx (stamp s.term (plastIndex s)))) x) ∧
      s' = psendMsgs (pappend s (es.mapIdx (stamp s.term (plastIndex s))))
        ([pselfAck id (pappend s (es.mapIdx (stamp s.term (plastIndex s))))] ++ ms)
  else if s.role = .follower ∧ s.lead ≠ W64 0 then
    s' = psendMsgs s [Msg.mkV .propose id s.lead (W64 0) m.reject m.index m.logterm m.commit
                        m.rejecthint m.entries [] m.ctx]
  else s' = s

/-- **`Step`'s type switch and the role's step function** at `s` (the state after the preamble):
a vote request answered (`Step`'s `MsgVote` arm, `raft.go:1167-1213`: granted when `canVote` and
the candidate's log is up to date, the vote recorded, the answer at the request's term; rejected
at the node's term); then by role (`stepFollower`, `stepCandidate`, `stepLeader`): a vote
response tallied by a candidate (`poll`: pending, won `WinEnd`, or lost back to a follower with no
leader); a `MsgApp` or `MsgHeartbeat` at a non-leader adopting the sender as leader then
`handleAppendEntries` (`AppEnd`) or `handleHeartbeat` (`commitTo(m.Commit)`, the response echoing
the context); a leader's `MsgAppResp` (`AppRespEnd`) and `MsgHeartbeatResp` (`sendAppend` to the
sender, `SendsEnd`; the read-index path is outside the scope); a proposal (`ProposeEnd`). A leader
ignores `MsgApp`/`MsgHeartbeat` of its term, a non-leader the responses to a leader, a
non-candidate the vote responses. Other types (outside the harness's inputs): some `StepC`
derivation. -/
def HandleEnd (_k : NodeK) (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  match m.ty with
  | .vote =>
    (PCanVote s m.src ∧ plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true ∧
      s' = psendMsgs { s with vote := m.src } [Msg.plain .voteResp id m.src m.term false]) ∨
    (¬ (PCanVote s m.src ∧ plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true) ∧
      s' = psendMsgs s [Msg.plain .voteResp id m.src s.term true])
  | .voteResp =>
    if s.role = .candidate then
      (¬ JLost c (recordVote s.votes m.src (!m.reject)) ∧
        s' = { s with votes := recordVote s.votes m.src (!m.reject) }) ∨
      (JQuorum c (granted (recordVote s.votes m.src (!m.reject))) ∧
        WinEnd c id { s with votes := recordVote s.votes m.src (!m.reject) } s') ∨
      (JLost c (recordVote s.votes m.src (!m.reject)) ∧
        s' = pbecomeFollower { s with votes := recordVote s.votes m.src (!m.reject) } s.term
               (W64 0))
    else s' = s
  | .app => if s.role = .leader then s' = s else AppEnd id (padoptLeader s m.src) m s'
  | .heartbeat =>
    if s.role = .leader then s' = s
    else s' = psendMsgs { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
                [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }]
  | .appResp => if s.role = .leader then AppRespEnd c id s m s' else s' = s
  | .heartbeatResp => if s.role = .leader then SendsEnd c id s s' else s' = s
  | .propose => ProposeEnd c id s m s'
  | _ => ∃ (B : Int) (r : List Msg), StepC c id B s r s'

/-- **The end state of `raft.Step` on a message `m`** (static mode, pre-vote and check-quorum off;
`raft.go:1060-1260`), as the code's paths are: a local message (term `0`: a forwarded or local
`MsgProp`; `send` stamps no term on it) goes to the type switch with no preamble; a stale one
(`m.Term < r.Term`) is ignored (no answer with check-quorum and pre-vote off); otherwise the
preamble (`PreEnd`), then the type switch (`HandleEnd`). -/
def RecvEnd (k : NodeK) (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (m.term = W64 0 ∧ HandleEnd k c id s m s') ∨
  (m.term ≠ W64 0 ∧ uint.Z m.term < uint.Z s.term ∧ s' = s) ∨
  (m.term ≠ W64 0 ∧ ∃ s1, PreEnd k s m s1 ∧ HandleEnd k c id s1 m s')

/-- **A tick's step** (`tickElection`'s `MsgHup`, `tickHeartbeat`'s `MsgBeat`; `raft.go:820-870`):
nothing; a campaign (`hup`, `campaign(campaignElection)`: a non-leader voter becomes a candidate
at the next term voting for itself, queues its own vote and a request to every other voter, with
its last entry id: `StepC.campaign`); or a leader's heartbeats (`bcastHeartbeat`,
`HeartbeatOk`: `Commit: min(Match, committed)`; `sendHeartbeat` sets only `To`, `Type`, `Commit`,
`Context`, so no index, log term or entries; #33 S4, msgShape: no context either, the context being
`hbCtx` of the read-only queue, empty in the harness's scope; #33 S4, destinations: to a peer of
the configuration, `c.ids`, as `bcastHeartbeat` visits the progress map). -/
def TickEnd (_k : NodeK) (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  s' = s ∨
  (s.role ≠ .leader ∧ id ∈ c.voters ∧
    ∃ (peers : List w64) (cl : List w8), peers ≡ₚ elements (c.voters \ {[id]}) ∧
      s' = psendMsgs (pbecomeCandidate id s)
        ([Msg.plain .voteResp id id (s.term + W64 1) false] ++
         peers.map (fun d => pvoteReq id d (s.term + W64 1) (plogLast s.base s.log) cl))) ∨
  (s.role = .leader ∧ ∃ ms : List Msg, (∀ x ∈ ms, HeartbeatOk id s x ∧ x.index = W64 0 ∧ x.logterm = W64 0 ∧ x.entries = [] ∧
      x.ctx = hbCtx s.rd.ro ∧ x.dst ∈ c.ids) ∧ s' = psendMsgs s ms)

/-- **`Advance`** (`rawnode.go:480-500`): the queued self-addressed messages `qs` (a leader's
self-acknowledgement, a candidate's self-vote) stepped in order (`RecvEnd`); the storage
acknowledgements leave `PState` as it is (`AckEnd`). -/
inductive AdvanceEnd (k : NodeK) (c : CfgM) (id : w64) : PState → List Msg → PState → Prop
  | nil (s : PState) : AdvanceEnd k c id s [] s
  | cons (s s1 s' : PState) (q : Msg) (qs : List Msg) :
      RecvEnd k c id s q s1 → AdvanceEnd k c id s1 qs s' → AdvanceEnd k c id s (q :: qs) s'

/-- (antithesis parity, design §1.2) `campaignTransfer`'s context bytes (`raft.go`:
`[]byte(campaignTransfer)`), on a transfer's vote requests. -/
def ctxTransfer : List w8 := go!"CampaignTransfer"

/-- (antithesis parity, design §1.2) **`campaign(t)`** at `s` (`raft.go:1045-1090`), `TickEnd`'s
campaign arm as a relation, with the request context `cl` (`[]` for an election, `ctxTransfer` for a
transfer). -/
def CampaignEnd (c : CfgM) (id : w64) (s : PState) (cl : List w8) (s' : PState) : Prop :=
  id ∈ c.voters ∧ ∃ peers : List w64, peers ≡ₚ elements (c.voters \ {[id]}) ∧
    s' = psendMsgs (pbecomeCandidate id s)
      ([Msg.plain .voteResp id id (s.term + W64 1) false] ++
       peers.map (fun d => pvoteReq id d (s.term + W64 1) (plogLast s.base s.log) cl))

/-- (antithesis parity, design §1.2) **A pre-campaign** (`campaign(campaignPreElection)`): no term
change, the leader hint cleared, the self pre-vote at the next term queued, a pre-vote request to
every other voter. -/
def PreCampaignEnd (c : CfgM) (id : w64) (s : PState) (s' : PState) : Prop :=
  id ∈ c.voters ∧ ∃ peers : List w64, peers ≡ₚ elements (c.voters \ {[id]}) ∧
    s' = psendMsgs { s with role := .follower, lead := W64 0, votes := ∅ }
      ([Msg.plain .preVoteResp id id (s.term + W64 1) false] ++
       peers.map (fun d => { pvoteReq id d (s.term + W64 1) (plogLast s.base s.log) [] with ty := .preVote }))

/-! ### The `RState` relations (antithesis parity, design §1.3)

The final relations are over `RState` (`Protocol/StepR.lean`): the `PState` relations above, as the
protocol content, wrapped with how the bookkeeping fields (`applied`, `pci`, `snap`, `cidx`, `cfg`,
`fp`) move. The configuration the `PState` relations read is the node's, `r.cfg.cfg`. -/

/-- The bookkeeping fields an input leaves. -/
def KeepCfg (r r' : RState) : Prop :=
  r'.applied = r.applied ∧ r'.cidx = r.cidx ∧ r'.cfg = r.cfg

/-- `pendingConfIndex` after a step to `p'` (`reset` clears it at every `becomeX` but
`becomePreCandidate`; `becomeLeader` sets it to the last index before its empty entry): a leader
still leading keeps it (but `RecvEndR`'s accepted batch). -/
def PciNext (r : RState) (p' : PState) : w64 :=
  if p'.role = .leader then (if r.p.role = .leader then r.pci else W64 (plogLastIndexZ r.p.base r.p.log))
  else W64 0

/-- The ghost prefix and the restored flag after a step to `p'`: a restore takes a full prefix
admissible at the snapshot (`StepR.snapRestore`'s premises); anything else keeps them. -/
def FpNext (Adm : List EntryM → CCState → Prop) (id : w64) (r : RState) (m : Msg) (p' : PState)
    (fp' : List EntryM) (sn' : Bool) : Prop :=
  (p'.base = r.p.base ∧ fp' = r.fp ∧ sn' = r.snap) ∨
  (m.ty = .snap ∧ p'.base = entryID.mk m.logterm m.index ∧ sn' = true ∧
    FullOk (entryID.mk m.logterm m.index) fp' ∧ r.full.take (uint.nat r.p.commit) <+: fp' ∧
    ∃ cs', id ∈ cs'.cfg.ids ∧ Adm fp' cs')

/-- **A received message** at `r` (`RawNode.Step` on a protocol message): `RecvEnd` at the node's
current configuration, the bookkeeping moved by `PciNext` and `FpNext`, and a leader's accepted
proposal batch exactly `propBatch`'s (the conf-change loop with `pendingConfIndex`, what the
binding's `AllSwitched`, B 246, needs). -/
def RecvEndR (Adm : List EntryM → CCState → Prop) (k : NodeK) (id : w64) (r : RState) (m : Msg)
    (r' : RState) : Prop :=
  RecvEnd k r.cfg.cfg id r.p m r'.p ∧ KeepCfg r r' ∧ FpNext Adm id r m r'.p r'.fp r'.snap ∧
  ((m.ty = .propose ∧ r.p.role = .leader ∧ r'.p.log ≠ r.p.log) →
      ∃ cs, CCTypesOk m.entries cs ∧
        r'.p.log = r.p.log ++ ((propBatch r m.entries cs).1.mapIdx (stamp r.p.term (plastIndex r.p))) ∧
        r'.pci = (propBatch r m.entries cs).2) ∧
  (¬ (m.ty = .propose ∧ r.p.role = .leader ∧ r'.p.log ≠ r.p.log) → r'.pci = PciNext r r'.p)

/-- **A tick** at `r`: `TickEnd` at the node's configuration, the bookkeeping kept but
`pendingConfIndex` (`PciNext`). -/
def TickEndR (k : NodeK) (id : w64) (r r' : RState) : Prop :=
  TickEnd k r.cfg.cfg id r.p r'.p ∧ KeepCfg r r' ∧ r'.fp = r.fp ∧ r'.snap = r.snap ∧
  r'.pci = PciNext r r'.p

/-- **`Advance` / a storage acknowledgement** (`appliedTo`, `appliedSnap`): nothing, the applied index
moved along committed entries (`StepR.advance`), or a pending snapshot applied, the configuration
switched to the snapshot's (`StepR.applySnap`). (The design's fourth arm, a joint configuration's
automatic leave, `AutoLeaveEnd`, comes with B3.) -/
def AckEndR (dec : CCDec) (Adm : List EntryM → CCState → Prop) (id : w64) (r r' : RState) : Prop :=
  (r' = r) ∨
  (∃ a, StepR Adm dec id 0 r [] { r with applied := a, cidx := max r.cidx (uint.nat a) } ∧
        r' = { r with applied := a, cidx := max r.cidx (uint.nat a) }) ∨
  (∃ j sn cs', StepR Adm dec id 0 r [] { r with applied := j, snap := sn, cidx := uint.nat j, cfg := cs' } ∧
        r' = { r with applied := j, snap := sn, cidx := uint.nat j, cfg := cs' })

/-- **`Advance`** at `r` (`AdvanceEnd`'s `RState` form): the queued self-addressed messages stepped in
order (`RecvEndR`), and the storage acknowledgements (`AckEndR`). -/
inductive AdvanceEndR (Adm : List EntryM → CCState → Prop) (dec : CCDec) (k : NodeK) (id : w64) :
    RState → List Msg → RState → Prop
  | nil (r r' : RState) : AckEndR dec Adm id r r' → AdvanceEndR Adm dec k id r [] r'
  | cons (r r1 r' : RState) (q : Msg) (qs : List Msg) :
      RecvEndR Adm k id r q r1 → AdvanceEndR Adm dec k id r1 qs r' → AdvanceEndR Adm dec k id r (q :: qs) r'

/-- `hasUnappliedConfChanges` (`raft.go:1013`): a conf entry committed and not applied. -/
def UnappliedConf (r : RState) : Prop :=
  ∃ (k : Nat) (e : EntryM), uint.nat r.applied ≤ k ∧ k < uint.nat r.p.commit ∧ r.full[k]? = some e ∧
    IsConfEnt e

/-- **`RawNode.Campaign`** (`MsgHup`, `campaignElection` or, with pre-vote, `campaignPreElection`;
`hup`'s guards: not a leader, promotable, no committed conf change unapplied): nothing, or the
campaign: an election's requests carry no context (`[]`). -/
def CampaignEndR (k : NodeK) (id : w64) (r r' : RState) : Prop :=
  (r' = r ∨
   (r.p.role ≠ .leader ∧ ¬ UnappliedConf r ∧ r.snap = false ∧
     (k.prevote = false ∧ CampaignEnd r.cfg.cfg id r.p [] r'.p ∨
      k.prevote = true ∧ PreCampaignEnd r.cfg.cfg id r.p r'.p))) ∧
  KeepCfg r r' ∧ r'.fp = r.fp ∧ r'.snap = r.snap ∧ r'.pci = PciNext r r'.p

/-- **`RawNode.TransferLeader(to)`** (local `MsgTransferLeader`; `raft.go:1450-1490`) at a leader:
ignored (a learner or itself as target, the same transfer pending, R1: `leadTransferee` hidden), or
recorded, and then either a `MsgTimeoutNow` to `to` (its `Match` the last index) or a probe
(`sendAppend`). The `MsgTimeoutNow` has no `Msg` reading (`mtypeOf 14 = none`): it is the `XMsg`
result. At a follower, forwarded to the leader (also an `XMsg`); otherwise dropped. -/
def TransferEndR (id : w64) (r : RState) (to : w64) (r' : RState) (xs : List XMsg) : Prop :=
  r'.applied = r.applied ∧ r'.cidx = r.cidx ∧ r'.cfg = r.cfg ∧ r'.fp = r.fp ∧ r'.snap = r.snap ∧
  r'.pci = r.pci ∧
  (if r.p.role = .leader then
     (r'.p = r.p ∧ xs = []) ∨
     (to ∈ r.cfg.cfg.voters ∧ to ≠ id ∧
       ((r.p.matched !! to = some (W64 (plogLastIndexZ r.p.base r.p.log)) ∧ r'.p = r.p ∧
          xs = [⟨.timeoutNow, id, to, r.p.term⟩]) ∨
        (xs = [] ∧ SendsEnd r.cfg.cfg id r.p r'.p)))
   else if r.p.lead ≠ W64 0 then r'.p = r.p ∧ xs = [⟨.transferLeader, to, r.p.lead, W64 0⟩]
   else r'.p = r.p ∧ xs = [])

/-- **A received `MsgTimeoutNow`** (`stepFollower`, `raft.go:1620`): a stale one ignored; otherwise
after the preamble (a higher term: `becomeFollower(x.term, None)`, the design's `PreEnd` at a
non-leader type, written out), a promotable node campaigns at once (`campaignTransfer`, no
pre-vote, `ctxTransfer` on its requests); otherwise nothing. -/
def TimeoutNowEndR (id : w64) (r : RState) (x : XMsg) (r' : RState) : Prop :=
  (uint.Z x.term < uint.Z r.p.term ∧ r' = r) ∨
  (uint.Z r.p.term ≤ uint.Z x.term ∧
    (∃ p1, (uint.Z r.p.term < uint.Z x.term ∧ p1 = pbecomeFollower r.p x.term (W64 0) ∨
              x.term = r.p.term ∧ p1 = r.p) ∧
       (r'.p = p1 ∨ CampaignEnd r.cfg.cfg id p1 ctxTransfer r'.p)) ∧
    KeepCfg r r' ∧ r'.fp = r.fp ∧ r'.snap = r.snap ∧ r'.pci = PciNext r r'.p)

/-- **`RawNode.ReportSnapshot`** (`MsgSnapStatus`; design §1.4, B3): nothing, or at a leader a probe
(`sendAppend`, `SendsEnd`), the bookkeeping kept. -/
def SnapStatusEndR (id : w64) (r r' : RState) : Prop :=
  r' = r ∨ (r.p.role = .leader ∧ SendsEnd r.cfg.cfg id r.p r'.p ∧ r' = { r with p := r'.p })

/-- **`RawNode.ApplyConfChange`** of the next conf entry (`StepR.applyConf`'s right-hand side, the
leader's step-down on removal with `StepDownOnRemoval`, `switchToConfig`): the entry committed,
after the configuration index, the conf entries between decoder-rejected. -/
def ApplyConfEndR (dec : CCDec) (Adm : List EntryM → CCState → Prop) (k : NodeK) (id : w64)
    (r : RState) (kk : Nat) (r' : RState) (xs : List Msg) : Prop :=
  ∃ (e : EntryM) (op : CCOp) (cs' : CCState) (p1 : PState),
    r.cidx ≤ kk ∧ kk < uint.nat r.p.commit ∧ r.full[kk]? = some e ∧ IsConfEnt e ∧
    NoUndecConfIn dec r.full r.cidx kk ∧ dec (r.full.take kk) e = some (.apply op) ∧
    ccStepB op r.cfg = some cs' ∧ Adm (r.full.take (kk + 1)) cs' ∧
    (p1 = r.p ∨ (r.p.role = .leader ∧ k.sdr = true ∧ id ∉ cs'.cfg.voters ∧
                 p1 = pbecomeFollower r.p r.p.term (W64 0))) ∧
    -- a leader still leading probes the new peers and may commit (`maybeCommit` at the new quorum)
    (r'.p = p1 ∨ (p1.role = .leader ∧ ∃ n, (n = p1.commit ∨ PCommitOk cs'.cfg p1 n) ∧
                   SendsEnd cs'.cfg id { p1 with commit := n } r'.p)) ∧
    r' = { r with p := r'.p, cidx := kk + 1, cfg := cs', pci := PciNext r r'.p } ∧ xs = []

/-- **The async storage responses** (B2; `MsgStorageAppendResp`/`MsgStorageApplyResp` stepped back):
the acknowledgement's effect (`AckEndR`), then the write's `Responses` stepped (`AdvanceEndR`). -/
def StoreAckEndR (Adm : List EntryM → CCState → Prop) (dec : CCDec) (k : NodeK) (id : w64)
    (r : RState) (resp : List Msg) (r' : RState) : Prop :=
  ∃ r1, AckEndR dec Adm id r r1 ∧ AdvanceEndR Adm dec k id r1 resp r'

end input_end

end EtcdGrove
end Perennial
