# Antithesis parity, B0: the final-scope statements (#33)

Scope: `~/coordinator-notes/plans/antithesis-parity-plan.md` §3 (B0). Every statement below is the
one the final theorem uses; B1-B4 add arms, report kinds and mode flags, and never restate. Labels:
B = `EtcdBinding.tla` line, R = `EtcdRaft.tla` line, file paths are relative to the worktree root
(`Proof/go_etcd_io/raft/v3/` is abbreviated `raft/`, `Proof/.../examples/raft/antithesis/` is
abbreviated `ant/`). Code citations are to the fork at `RAFT_REV = d2c16c5` (`etc/goose.py:71`).
Statements only, no proofs. Where a name below is new it is marked **new**; everything else exists
today with the cited text.

Three rules fix the design:

* **R1. Exactness, not determinism.** An end relation must be true of raft and strong enough for the
  Sim. Where `PState` hides the state that decides a path (the lease's `electionElapsed`, a
  pre-candidate's tally, `recentActive`, `leadTransferee`), the arm is a disjunction over the
  hidden choice. Nothing below asks the Sim to know which disjunct ran.
* **R2. Two kinds of guard.** A *node constant* `k : NodeK` (Go `Config.PreVote`,
  `CheckQuorum`, `StepDownOnRemoval`) guards an arm that is raft's real behaviour. A *scope mode*
  `md : RnMode` (§2) guards what a RawNode spec promises: which inputs have an exact effect, and
  which state facts hold. A batch proves its feature by extending the lifting lemmas and setting its
  `md` flag. The relations in §1 are unconditional definitions. They are proved one input type at a
  time, and that proof is what the mode flags gate.
* **R3. One program per batch boundary.** The driver draws the run's mode at random under a Go
  constant mask `scope` (`examples/raft/antithesis/main.go`, **new**, the driver helper's).
  Each interim theorem is about the program with that batch's mask. The Lean `RnMode`
  value `mdB1`, `mdB2`, ... is that mask. The final mask is all true. No top-level premise is
  needed (§3.6).

## 1. The per-input end relations

### 1.1 The state: `RState`, not `PState` plus a fixed configuration

The final relations are over `RState` (`raft/Protocol/StepR.lean:87`, exists): `p : PState`,
`applied`, `pci` (`pendingConfIndex`), `snap` (a restored snapshot not yet applied), `cidx`,
`cfg : CCState` (the configuration of the full log's first `cidx` entries, `RInv`), and `fp` (the
ghost prefix below `p.base`). This gives everything the brief lists:

* a configuration that varies with the log is `r.cfg.cfg` (joint: `outgoing`, learners,
  `learnersNext`, `autoLeave`);
* an arbitrary log base is `r.p.base`, with the full log `r.full = r.fp ++ r.p.log`, which is what the
  binding's whole log is (`S.log[n]`, never compacted: B 155-194, 634-650);
* `applied`, `pci` and `cidx` are what conf proposals (`propBatch`, `StepR.lean:123`),
  `hasUnappliedConfChanges` (`raft.go:1013`) and `ApplyConfChange` read.

`StepR` already has every rule over `RState` (`snapRestore`, `applySnap`, `applyConf`, `advance`,
`stepDown`, the reads). `InputEnd` keeps its `PState` relations word for word, as the protocol
content, and wraps them in `RState` relations that say how the bookkeeping fields move.

```lean
/-- (new) A node's `Config` flags the end relations read (`newRaft` copies them, nothing writes them):
`PreVote`, `CheckQuorum`, `StepDownOnRemoval`. -/
structure NodeK where
  prevote : Bool := false
  cq : Bool := false
  sdr : Bool := false

/-- (new) The `RState` reading of a node (`ownRawNodeAt`'s `"%Hps"`, §4.1). -/
def toRState (rs : RNState) (fp : List EntryM) (s : NState) : RState :=
  { p := toPState s, applied := s.logst.applied, pci := s.pci,
    snap := decide (s.logst.snap ≠ none), cidx := rs.capplied, cfg := rs.cfg, fp := fp }
```

### 1.2 The `PState` relations: existing arms kept, new arms added

Every existing definition of `raft/Protocol/InputEnd.lean` keeps its body. The changes are a `k`
argument, new disjuncts, and new `match` arms in place of the `_ => StepC` fallback. A proof of an
existing arm adapts with `Or.inl` or the same `match` reduction (§5).

```lean
/-- (new) The types `Step`'s preamble does not turn into a follower at a higher term
(`raft.go:1063-1090`): a pre-vote request, a granted pre-vote response. -/
def PreKeep (m : Msg) : Prop := m.ty = .preVote ∨ (m.ty = .preVoteResp ∧ m.reject = false)

/-- `PreEnd`: today's arms (the first now excluding `PreKeep`), and the pre-vote arm. -/
def PreEnd (k : NodeK) (s : PState) (m : Msg) (s1 : PState) : Prop :=
  (uint.Z s.term < uint.Z m.term ∧ ¬ PreKeep m ∧
    s1 = pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0)) ∨
  (m.term = s.term ∧ s1 = s) ∨
  (k.prevote = true ∧ uint.Z s.term < uint.Z m.term ∧ PreKeep m ∧ s1 = s)
```

`PreKeep` holds only for pre-vote types, so with `k.prevote = false` the first arm is today's
(`PreKeep m` is false for the harness's types today).

**The lease and stale arms** (new arms of `RecvEnd`): with `CheckQuorum` on, a vote or pre-vote
request of a higher term at a node in its lease is ignored (`raft.go:1066-1078`; `force` is the
`campaignTransfer` context). With `CheckQuorum` or `PreVote` on, a stale `MsgApp` or `MsgHeartbeat`
is answered by an empty `MsgAppResp` at the node's term (`raft.go:1093-1112`, `StepC.zeroAck`'s form),
and a stale `MsgPreVote` by a rejection (`raft.go:1121-1130`). By R1 the lease is a disjunct: the
node's `electionElapsed` is not in `PState`.

```lean
/-- (new) `campaignTransfer`'s context bytes (`raft.go`: `[]byte(campaignTransfer)`). -/
def ctxTransfer : List w8 := go!"CampaignTransfer"

def LeaseIgnore (k : NodeK) (s : PState) (m : Msg) : Prop :=
  k.cq = true ∧ (m.ty = .vote ∨ m.ty = .preVote) ∧ uint.Z s.term < uint.Z m.term ∧
    s.lead ≠ W64 0 ∧ m.ctx ≠ ctxTransfer

def StaleEnd (k : NodeK) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  s' = s ∨
  ((k.cq = true ∨ k.prevote = true) ∧ (m.ty = .app ∨ m.ty = .heartbeat) ∧
    s' = psendMsgs s [Msg.mk .appResp id m.src s.term false (W64 0) (W64 0) (W64 0) (W64 0) []]) ∨
  (m.ty = .preVote ∧ s' = psendMsgs s [Msg.plain .preVoteResp id m.src s.term true])

def RecvEnd (k : NodeK) (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (m.term = W64 0 ∧ HandleEnd k c id s m s') ∨
  (m.term ≠ W64 0 ∧ uint.Z m.term < uint.Z s.term ∧ StaleEnd k id s m s') ∨  -- was `s' = s`
  (m.term ≠ W64 0 ∧ LeaseIgnore k s m ∧ s' = s) ∨                         -- new
  (m.term ≠ W64 0 ∧ ¬ LeaseIgnore k s m ∧ ∃ s1, PreEnd k s m s1 ∧ HandleEnd k c id s1 m s')
```

Today's stale arm `s' = s` is `StaleEnd`'s first disjunct. With `k.cq = false`, `LeaseIgnore` is
false.

**`HandleEnd`**: the seven arms of today stay word for word (`vote`, `voteResp`, `app`,
`heartbeat`, `appResp`, `propose`), except one. `heartbeatResp` gains the read acknowledgement. The
fallback `_ => ∃ B r, StepC …` is replaced by exact arms, and the match is total over `MsgType`:

```lean
def HandleEnd (k : NodeK) (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  match m.ty with
  | .vote => …                                   -- today's text
  | .voteResp => …                               -- today's text
  | .app => …                                    -- today's text
  | .heartbeat => …                              -- today's text (it already echoes `m.ctx`)
  | .appResp => …                                -- today's text
  | .propose => ProposeEnd c id s m s'           -- today's text
  | .heartbeatResp =>                            -- today's arm, then the read acknowledgement
    if s.role = .leader then
      ∃ s2, SendsEnd c id s s2 ∧ (m.ctx = [] ∧ s' = s2 ∨ m.ctx ≠ [] ∧ ReadAckEnd c id s2 m s')
    else s' = s
  | .preVote => PreVoteEnd id s m s'
  | .preVoteResp =>
    if s.role = .follower ∧ s.lead = W64 0 then s' = s ∨ CampaignEnd c id s [] s' else s' = s
  | .readIndex => ReadIdxEnd c id s m s'
  | .readIndexResp =>
    (∃ e, m.entries = [e] ∧ s' = { s with rd := { s.rd with states := s.rd.states ++ [⟨m.index, e.Data'⟩] } }) ∨
    (m.entries.length ≠ 1 ∧ s' = s)
  | .snap => if s.role = .leader then s' = s else SnapEnd id (padoptLeader s m.src) m s'
```

The `heartbeatResp` arm with `m.ctx = []` is today's `SendsEnd c id s s'` (take `s2 = s'`). The
`preVoteResp` arm is R1: a pre-candidate reads as a follower with no leader (`toPState`,
`raft/Defs.lean:1567-1569`, whose tally is hidden). Loss is `becomeFollower(r.Term, None)`, which
leaves `PState` as it is. A win is `campaign(campaignElection)`.

```lean
/-- (new) `Step`'s `MsgPreVote` answer (`raft.go:1167-1213`): granted when the candidate's log is up
to date and the node could vote for it, or the request is of a later term; at the request's term when
granted, the node's otherwise; nothing recorded. -/
def PreVoteEnd (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  ((PCanVote s m.src ∨ uint.Z s.term < uint.Z m.term) ∧
      plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true ∧
      s' = psendMsgs s [Msg.plain .preVoteResp id m.src m.term false]) ∨
  (¬ ((PCanVote s m.src ∨ uint.Z s.term < uint.Z m.term) ∧
      plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true) ∧
      s' = psendMsgs s [Msg.plain .preVoteResp id m.src s.term true])

/-- (new) `campaign(t)` at `s` (`raft.go:1045-1090`), today's `TickEnd` campaign arm as a relation,
with the request context `cl` (`[]` for an election, `ctxTransfer` for a transfer). -/
def CampaignEnd (c : CfgM) (id : w64) (s : PState) (cl : List w8) (s' : PState) : Prop :=
  id ∈ c.voters ∧ ∃ peers : List w64, peers ≡ₚ elements (c.voters \ {[id]}) ∧
    s' = psendMsgs (pbecomeCandidate id s)
      ([Msg.plain .voteResp id id (s.term + W64 1) false] ++
       peers.map (fun d => pvoteReq id d (s.term + W64 1) (plogLast s.base s.log) cl))

/-- (new) A pre-campaign (`campaign(campaignPreElection)`): no term change, the leader hint
cleared, the self pre-vote at the next term queued, a pre-vote request to every other voter. -/
def PreCampaignEnd (c : CfgM) (id : w64) (s : PState) (s' : PState) : Prop :=
  id ∈ c.voters ∧ ∃ peers : List w64, peers ≡ₚ elements (c.voters \ {[id]}) ∧
    s' = psendMsgs { s with role := .follower, lead := W64 0, votes := ∅ }
      ([Msg.plain .preVoteResp id id (s.term + W64 1) false] ++
       peers.map (fun d => { pvoteReq id d (s.term + W64 1) (plogLast s.base s.log) [] with ty := .preVote }))

/-- (new) `stepLeader`'s / `stepFollower`'s `MsgReadIndex` (`raft.go:1341-1365, 1600-1610`;
`ReadOnlySafe`): a single voter answers at once; a leader with no entry of its term committed
defers; otherwise the request is recorded with its own acknowledgement and a heartbeat with its
context goes to the peers; a follower with a leader forwards it; otherwise it is dropped. -/
def ReadIdxEnd (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  if s.role = .leader then
    (plogTermAt s.base s.log s.commit ≠ some s.term ∧ ∃ pm : MessageM, m.src = pm.From' ∧
      s' = { s with rd := { s.rd with pend := s.rd.pend ++ [(pm, m.entries)] } }) ∨
    (plogTermAt s.base s.log s.commit = some s.term ∧ CfgSingle c id ∧
      s' = preadRespondAll id s [⟨s.commit, m.src, m.entries⟩]) ∨
    (plogTermAt s.base s.log s.commit = some s.term ∧ ¬ CfgSingle c id ∧
      ∃ ms : List Msg,
        (∀ x ∈ ms, HbSendOk c id s x ∧ x.ctx = readCtx m.entries) ∧
        s' = psendMsgs { s with rd := { s.rd with
               ro := readonlyArrive s.rd.ro id ⟨s.commit, m.src, m.entries⟩ } } ms)
  else if s.lead ≠ W64 0 then
    s' = psendMsgs s [{ m with src := if m.src = W64 0 then id else m.src, dst := s.lead, term := W64 0 }]
  else s' = s

/-- (new) A read acknowledgement at the leader (`StepC.readAck`'s right-hand side, the quorum
an existential: `readonlyAdvance` at the first acknowledged position, or no quorum yet). -/
def ReadAckEnd (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (¬ ∃ N, JQuorumAcked c (fun v => ((readonlyRecvAck s.rd.ro m.src m.ctx).acks !! v).getD (W64 0)) N) ∧
    s' = { s with rd := { s.rd with ro := readonlyRecvAck s.rd.ro m.src m.ctx } } ∨
  ∃ N, JQuorumAcked c (fun v => ((readonlyRecvAck s.rd.ro m.src m.ctx).acks !! v).getD (W64 0)) N ∧
    s' = preadRespondAll id
      { s with rd := { s.rd with ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } }
      (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2

/-- (new) `handleSnapshot` (`raft.go:1830-1860`) at a non-leader that adopted the sender: restored
(the log replaced at the snapshot's id, `StepC.snapRestore`), fast-forwarded (`snapFastfwd`) or
stale (`snapStale`), each answered with an `MsgAppResp`. The configuration is not switched here:
the fork switches at apply (`StepR.applySnap`, §6.3). -/
def SnapEnd (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (uint.Z s.commit < uint.Z m.index ∧ ¬ PlogMatches s.base s.log (entryID.mk m.logterm m.index) ∧
    s' = psendMsgs { s with base := entryID.mk m.logterm m.index, log := [], commit := m.index }
      [Msg.mk .appResp id m.src s.term false m.index (W64 0) (W64 0) (W64 0) []]) ∨
  (uint.Z s.commit < uint.Z m.index ∧ PlogMatches s.base s.log (entryID.mk m.logterm m.index) ∧
    s' = psendMsgs { s with commit := m.index }
      [Msg.mk .appResp id m.src s.term false m.index (W64 0) (W64 0) (W64 0) []]) ∨
  (uint.Z m.index ≤ uint.Z s.commit ∧
    s' = psendMsgs s [Msg.mk .appResp id m.src s.term false s.commit (W64 0) (W64 0) (W64 0) []])
```

`HbSendOk c id s x` (**new**, a name for today's conjunction) is `HeartbeatOk id s x ∧ x.index =
W64 0 ∧ x.logterm = W64 0 ∧ x.entries = [] ∧ x.dst ∈ c.ids`. `readCtx es` (**new**) is
`(es.head?.map EntryM.Data').getD []`, the context `sendMsgReadIndexResponse` broadcasts.

**`AppSendOk`** gains the snapshot disjunct, so the `NoSnapSent` hypothesis of the lifting lemmas
goes away at `md.snapshots`:

```lean
def SendOk (c : CfgM) (id : w64) (s : PState) (m : Msg) : Prop :=
  AppSendOk c id s m ∨ (m.ty = .snap ∧ SnapOk id s m ∧ m.dst ∈ c.ids)
```

`SnapOk` is `ReplOk`'s other disjunct, which exists. `WinEnd`, `SendsEnd`, `ProposeEnd` and
`TickEnd`'s broadcasts change `AppSendOk` to `SendOk`, a weakening. Each old proof adapts with
`Or.inl`.

**`TickEnd`**: today's three arms, plus the pre-campaign arm, plus the CheckQuorum step-down (R1:
`recentActive` is not in `PState`). The heartbeat arm's `x.ctx = []` becomes `x.ctx = hbCtx s.rd.ro`
(**new** name for `bcastHeartbeat`'s `lastPendingRequestCtx`). The two agree when
`ro.pending = []`, which is today's scope.

```lean
def TickEnd (k : NodeK) (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  s' = s ∨
  (s.role ≠ .leader ∧ k.prevote = false ∧ CampaignEnd c id s [] s') ∨      -- today's campaign arm
  (s.role ≠ .leader ∧ k.prevote = true ∧ PreCampaignEnd c id s s') ∨       -- new
  (s.role = .leader ∧ ∃ ms : List Msg,
      (∀ x ∈ ms, HbSendOk c id s x ∧ x.ctx = hbCtx s.rd.ro) ∧ s' = psendMsgs s ms) ∨
  (s.role = .leader ∧ k.cq = true ∧ s' = pbecomeFollower s s.term (W64 0))  -- new
```

Today's campaign arm is literally `CampaignEnd c id s cl s'` with an existential `cl` (`HupGuard`'s).
B1 keeps the `∃ cl` form if `hup`'s spec still does not pin `cl = []`, and that does not affect the Sim.

### 1.3 The `RState` relations (new)

```lean
/-- The bookkeeping fields an input leaves. -/
def KeepCfg (r r' : RState) : Prop :=
  r'.applied = r.applied ∧ r'.cidx = r.cidx ∧ r'.cfg = r.cfg

/-- `pendingConfIndex` after a step to `p'` (`reset` clears it at every `becomeX` but
`becomePreCandidate`; `becomeLeader` sets it to the last index before its empty entry): a leader
still leading keeps it (but `ProposeEndR`'s accepted batch). -/
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

def TickEndR (k : NodeK) (id : w64) (r r' : RState) : Prop :=
  TickEnd k r.cfg.cfg id r.p r'.p ∧ KeepCfg r r' ∧ r'.fp = r.fp ∧ r'.snap = r.snap ∧
  r'.pci = PciNext r r'.p

/-- **`RawNode.Campaign`** (`MsgHup`, `campaignElection` or, with pre-vote, `campaignPreElection`;
`hup`'s guards: not a leader, promotable, no committed conf change unapplied): nothing, or the
campaign. -/
def CampaignEndR (k : NodeK) (id : w64) (r r' : RState) : Prop :=
  (r' = r ∨
   (r.p.role ≠ .leader ∧ ¬ UnappliedConf r ∧ r.snap = false ∧
     (k.prevote = false ∧ CampaignEnd r.cfg.cfg id r.p [] r'.p ∨
      k.prevote = true ∧ PreCampaignEnd r.cfg.cfg id r.p r'.p))) ∧
  KeepCfg r r' ∧ r'.fp = r.fp ∧ r'.snap = r.snap ∧ r'.pci = PciNext r r'.p

/-- `hasUnappliedConfChanges` (`raft.go:1013`): a conf entry committed and not applied. -/
def UnappliedConf (r : RState) : Prop :=
  ∃ (k : Nat) (e : EntryM), uint.nat r.applied ≤ k ∧ k < uint.nat r.p.commit ∧ r.full[k]? = some e ∧ IsConfEnt e

/-- **`RawNode.TransferLeader(to)`** (local `MsgTransferLeader`; `raft.go:1450-1490`) at a leader:
ignored (a learner or itself as target, the same transfer pending, R1: `leadTransferee` hidden), or
recorded, and then either a `MsgTimeoutNow` to `to` (its `Match` the last index) or a probe
(`sendAppend`). The `MsgTimeoutNow` has no `Msg` reading (`mtypeOf 14 = none`): it is the
`XMsg` result. At a follower, forwarded to the leader (also an `XMsg`); otherwise dropped. -/
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

/-- **A received `MsgTimeoutNow`** (`stepFollower`, `raft.go:1620`): after the preamble, a
promotable node campaigns at once (`campaignTransfer`, no pre-vote, `ctxTransfer` on its
requests); otherwise nothing. -/
def TimeoutNowEndR (id : w64) (r : RState) (x : XMsg) (r' : RState) : Prop :=
  (uint.Z x.term < uint.Z r.p.term ∧ r' = r) ∨
  (uint.Z r.p.term ≤ uint.Z x.term ∧ ∃ p1, PreEnd {} r.p ⟨…x as a Msg of type .app…⟩ p1 ∧
     (r'.p = p1 ∨ CampaignEnd r.cfg.cfg id p1 ctxTransfer r'.p)) ∧
  KeepCfg r r' ∧ r'.fp = r.fp ∧ r'.snap = r.snap ∧ r'.pci = PciNext r r'.p
```

**The two message types `Msg` does not have.** `MsgTransferLeader` and `MsgTimeoutNow` have no
`MsgType` constructor (`raft/Defs.lean:139-153`, `mtypeOf`'s `none` arm). Adding constructors would
put them under raft's message invariant (`isMessage`, `XfOk`, `GhostState.lean`'s matches): a raft
change with no Sim benefit. They carry only type, sender, receiver and term, and the binding checks
nothing more (`isUnmodelled`, `Binding.lean:702`). So they get their own record:

```lean
inductive XTy where | transferLeader | timeoutNow
structure XMsg where
  ty : XTy
  src : w64
  dst : w64
  term : w64
```

The preamble above is written with `PreEnd` at `fromLeader = false`. B1 writes it out:
`becomeFollower(x.term, None)` at a higher term.

**Applying.**

```lean
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

/-- **`Advance` / a storage acknowledgement** (`appliedTo`, `appliedSnap`): the applied index moved
along committed entries (`StepR.advance`), or a pending snapshot applied, the configuration switched
to the snapshot's (`StepR.applySnap`), and, in a joint configuration with `autoLeave`, the leader's
automatic leave proposed (`appliedTo`: an empty `ConfChangeV2`). -/
def AckEndR (dec : CCDec) (Adm : List EntryM → CCState → Prop) (id : w64) (r r' : RState) : Prop :=
  (r' = r) ∨
  (∃ a, StepR Adm dec id 0 r [] { r with applied := a, cidx := max r.cidx (uint.nat a) } ∧
        r' = { r with applied := a, cidx := max r.cidx (uint.nat a) }) ∨
  (∃ j sn cs', StepR Adm dec id 0 r [] { r with applied := j, snap := sn, cidx := uint.nat j, cfg := cs' } ∧
        r' = { r with applied := j, snap := sn, cidx := uint.nat j, cfg := cs' }) ∨
  (r.cfg.cfg.autoLeave = true ∧ r.p.role = .leader ∧ AutoLeaveEnd id r r')
```

`AutoLeaveEnd` (**new**, B3) is `ProposeEndR`'s accepted arm at the empty `ConfChangeV2`.

**`AdvanceEnd`** keeps its constructors over `RecvEnd`, and gets the `RState` form:

```lean
inductive AdvanceEndR (Adm) (dec : CCDec) (k : NodeK) (id : w64) : RState → List Msg → RState → Prop
  | nil (r r' : RState) : AckEndR dec Adm id r r' → AdvanceEndR Adm dec k id r [] r'
  | cons (r r1 r' : RState) (q : Msg) (qs : List Msg) :
      RecvEndR Adm k id r q r1 → AdvanceEndR Adm dec k id r1 qs r' → AdvanceEndR Adm dec k id r (q :: qs) r'
```

**Async storage (B2).** With `AsyncStorageWrites` the queued storage messages are not stepped by
`Advance`. Their responses come back through `RawNode.Step`: `MsgStorageAppendResp` (`stableTo`,
the self-responses of the write released) and `MsgStorageApplyResp` (`appliedTo`). The protocol
effect is `AckEndR`, and the release is the write's `Responses` stepped (their `RecvEndR`).
Neither is a `Msg` (no `mtypeOf`). They are a separate input, `Input.storeAck` (§3.4):

```lean
def StoreAckEndR (Adm) (dec) (k) (id) (r : RState) (resp : List Msg) (r' : RState) : Prop :=
  ∃ r1, AckEndR dec Adm id r r1 ∧ AdvanceEndR Adm dec k id r1 resp r'
```

### 1.4 Which arms exist, which are new, and their guards

| input | relation (arm) | today | new in | `md` flag that admits it in the spec |
|---|---|---|---|---|
| MsgApp, MsgHeartbeat | `HandleEnd .app/.heartbeat` | yes | none | always |
| stale MsgApp/MsgHeartbeat answered | `StaleEnd` arm 2 | no | B1 | `md.prevote ∨ md.cq` |
| MsgAppResp | `.appResp` | yes | none | always |
| MsgVote, MsgVoteResp | `.vote`, `.voteResp` | yes | none | always |
| vote ignored in lease | `LeaseIgnore` | no | B1 | `md.cq` |
| MsgPreVote, MsgPreVoteResp, pre-campaign | `PreVoteEnd`, `.preVoteResp`, `PreCampaignEnd`, `PreKeep` | no | B1 | `md.prevote` |
| CheckQuorum step-down | `TickEnd` arm 5 | no (`StepC.stepDown` only) | B1 | `md.cq` |
| MsgHeartbeat ctx, MsgHeartbeatResp ctx | `.heartbeat` (exists), `ReadAckEnd` | half | B1 | `md.reads` |
| MsgReadIndex (local, forwarded), MsgReadIndexResp | `ReadIdxEnd`, `.readIndexResp` | no | B1 | `md.reads` |
| MsgProp local | `.propose` (`ProposeEnd`) | yes | none | always |
| MsgProp from the network | the same arm, `RecvEndR`'s batch | yes (unused) | B1 | `md.forwarding` |
| Campaign | `CampaignEndR` | no (`TickEnd` arm) | B1 | always (the arm is `TickEnd`'s) |
| TransferLeader, MsgTimeoutNow | `TransferEndR`, `TimeoutNowEndR` | no | B1 | `md.transfer` |
| Unreachable | `r' = r` with `Match` unchanged (`StepEndTy`'s `MsgUnreachable`) | in `StepEnd` | B1 | always |
| MsgSnap | `SnapEnd`, `FpNext` arm 2, `SendOk` arm 2 | no | B3 | `md.snapshots` |
| ReportSnapshot (MsgSnapStatus) | `SnapStatusEndR`: `r' = r` but a probe (`SendsEnd`) | no | B3 | `md.snapshots` |
| ApplyConfChange | `ApplyConfEndR` | no (lower: `TracedApplyConfChange`) | B3 | `md.confChanges` |
| Advance / acks | `AdvanceEndR`, `AckEndR` | `AdvanceEnd` (acks = no-op) | B2/B3 | arm 2 always, arms 3-4 `md.snapshots`/`md.confChanges` |
| async storage responses | `StoreAckEndR` | no | B2 | `md.async` |

## 2. The scope predicate: `RnScope md`

```lean
/-- (new) The features a RawNode spec's exact effect covers (R2). `{}` is today's scope. -/
structure RnMode where
  prevote : Bool := false
  cq : Bool := false
  reads : Bool := false
  transfer : Bool := false
  forwarding : Bool := false
  snapshots : Bool := false
  confChanges : Bool := false
  async : Bool := false
  nonVoters : Bool := false   -- Server ⊋ InitVoters: a node outside its configuration

def RnScope (md : RnMode) (rs : RNState) (s : NState) : Prop :=
  (md.confChanges = false → rs.mode.isDyn = true → rs.cfg.cfg.outgoing = ∅) ∧
  (md.prevote = false → s.prevote = false) ∧ (md.cq = false → s.cq = false) ∧
  (md.reads = false → s.rd.pend = [] ∧ (s.role = .leader → s.rd.ro.pending = [])) ∧
  (md.snapshots = false → rs.slent = none ∧ s.logst.prev = base0 ∧ s.logst.snap = none ∧
     ∀ m ∈ s.outbox, m.ty ≠ .snap) ∧
  (md.transfer = false → s.gh.xs = false)

def RnCfgIn (md : RnMode) (γ : RaftNames) (id : w64) (rs : RNState) : Prop :=
  (md.nonVoters = false → id ∈ γ.reCfg) ∧
  (md.confChanges = false → (rs.mode.isDyn = true → rs.cfg.cfg.incoming = γ.reCfg) ∧
     rs.cfg.cfg.learners = ∅) ∧
  γ.reTrace = none ∧ rs.mode.isDyn = true

def rnScopeAt (γ : RaftNames) (id : w64) (sc : Option RnMode) (rs : RNState) (s : NState) : IProp GF :=
  match sc with
  | none => iprop(emp)
  | some md => iprop(⌜RnScope md rs s ∧ RnCfgIn md γ id rs⌝ ∗
                     □ (⌜md.snapshots = false⌝ -∗ storCapF s.logst.storage 0))
```

`ownRawNodeAt γ rn id rs ps qs ip sc` becomes `ownRawNodeAt γ rn id rs r qs ip (sc : Option RnMode)`.
Today's `false` is `none` and `true` is `some {}`. `"%Hps"` becomes `⌜toRState rs fp s = r⌝`, where
`fp` is the existential already in the body, and `"%Hasync"` becomes
`⌜md.async = false → rnv.asyncStorageWrites' = false⌝`.

| today's conjunct (file:line) | flag that lifts it |
|---|---|
| `isDyn → outgoing = ∅` (`RawNodeAt.lean:82`) | `confChanges` |
| `s.prevote = false` | `prevote` |
| `s.cq = false` | `cq` |
| `s.rd.pend = []`, `leader → ro.pending = []` | `reads` |
| `slent = none`, `prev = base0`, `snap = none`, no `MsgSnap` queued, `storCapF … 0` | `snapshots` |
| `s.gh.xs = false` | `transfer` |
| `RnCfgIn`: `id ∈ γ.reCfg` | `nonVoters` |
| `RnCfgIn`: `incoming = γ.reCfg`, `learners = ∅`; `rnCfg γ` in every form | `confChanges` |
| `ownRawNodeAt`'s `"%Hasync"` (`asyncStorageWrites' = false`, inherited from `ownRawNode`) | `async` |
| `antStepTypes` (`RawNodeAbsSpecs.lean:64`) | `stepTypes md` below |
| `LiftScope`'s `prevote = false ∧ cq = false ∧ role ≠ preCandidate` | `prevote`, `cq` (§5) |
| `LiftScope`'s `rd.pend = []` | `reads` |
| `LiftScope`'s `id ∈ domSet s.prvals` | `nonVoters` (only needed at a non-follower, `FnScope`'s form) |
| `emptyStartForm`'s `γ.bootLen = 0`, `cv.PreVote' = false ∧ cv.CheckQuorum' = false`, `cv.ID' ∈ vs` | `RunCfg.boot` (§3.1), `prevote`/`cq`, `nonVoters` |
| `Advance.form`'s `∀ q ∈ qs, q.ty ≠ .preVoteResp` | `prevote` |
| `Step.form`'s `MsgHeartbeatResp → ctx = []` | `reads` |
| `Step.form`'s `From ∈ γ.reCfg` | `confChanges`/`nonVoters`: `From ∈ γ.ids` and `errStepPeer` a new `r' = r` arm |

```lean
def stepTypes (md : RnMode) : List w32 :=
  antStepTypes ++ (if md.prevote then [MsgPreVote, MsgPreVoteResp] else []) ++
  (if md.reads then [MsgReadIndex, MsgReadIndexResp] else []) ++
  (if md.transfer then [MsgTransferLeader, MsgTimeoutNow] else []) ++
  (if md.forwarding then [MsgProp] else []) ++ (if md.snapshots then [MsgSnap] else []) ++
  (if md.async then [MsgStorageAppendResp, MsgStorageApplyResp] else [])
```

## 3. The Sim

### 3.1 The run's configuration and N servers: `Fin R.N`

```lean
structure RunCfg where
  N : Nat          -- servers raft1 … raftN
  K : Nat          -- initial voters raft1 … raftK
  boot : Bool      -- Bootstrapped: BootInit written into storage (their rawnode), not RawNode.Bootstrap
  k : Fin N → NodeK   -- each node's Config flags (drawn per run: equal across nodes in the driver)
  md : RnMode      -- the batch's mask (R3)
  hK : 1 ≤ K ∧ K ≤ N ∧ N ≤ 9

def RunCfg.cfg (R : RunCfg) : AntCheck.Config :=
  { server := AntCheck.setOf (namesL R.N), initVoters := AntCheck.setOf (namesL R.K),
    bootstrapped := R.boot }

def nodeId {N : Nat} (n : Fin N) : w64 := W64 ((n.val : Int) + 1)
def RunCfg.voters0 (R : RunCfg) : GSet w64 := GMap.listToSet ((List.range R.K).map fun i => W64 (i + 1))
def RunCfg.c0 (R : RunCfg) : CCState := ⟨CfgM.simple R.voters0 ∅, …⟩   -- the initial conf state
```

**`Fin R.N`, not a server list.** The binding indexes every per-server variable by position in
`cfg.server` (`State.idx`, `Types.lean:392`). `Fin R.N` with `Shape`'s lengths `= R.N` keeps each
`[n.val]!` in bounds by construction. It keeps today's `nodeId`, so every `∀ n : Fin 3` in the 45
files that mention it becomes `∀ n : Fin R.N`, mechanically. A list of ids would need
`idxOf?`/membership reasoning at every lookup. `N ≤ 9` keeps `setOf (namesL N) = namesL N` (string
order equals numeric order for `raft1`-`raft9`). The binding cfgs use `N ∈ {3, 5}`.
`Server ⊇ InitVoters` holds by `K ≤ N`.

### 3.2 `NodeView`: durable vs in-memory, the undo record, the configuration

```lean
/-- (new) What the binding holds as a node's disk: the last announced write
(`currentTerm`/`voteFor`/`log`/`commitIndex`, B 290-436). `log` is full, from index 1. -/
structure DurW where
  term : w64
  vote : w64
  commit : w64
  log : List EntryM
  deriving Inhabited

/-- (new) An announced in-memory state the write of which comes later (async, batch: `mem` with
`w = 1`, the binding's `queue[n]`, B 450-459), with what the `write` report will say. -/
structure MemRec where
  role : Role
  pre : Bool
  term : w64
  vote : w64
  commit : w64
  first : Nat
  ents : List EntryM
  snap : Option entryID
  cause : Option Msg
  byE : AntCheck.Str

structure NodeView where
  /-- raft's state between inputs, or at its last `Ready` in a drain (`toRState`) -/
  r : RState
  /-- the committed entries handed out (`RNState.delivered`); after a restore, the snapshot's prefix -/
  delivered : List EntryM
  /-- the binding's disk of the node (C1): the last announced write -/
  dur : DurW
  /-- the disk before that write while it is not made (`undo[n]`, B 349-359): restart may lose it -/
  undo : Option DurW := none
  /-- that write is made (`made`, B 496) -/
  made : Bool := true
  /-- async/batch: the announced states not yet written (`queue[n]`) -/
  mems : List MemRec := []
  /-- the configuration the binding counts with, and its index (`config[n]`, `confAt[n]`) -/
  conf : CCState
  confAt : Nat := 0
  /-- the last reported role was `precandidate` -/
  pre : Bool := false
  /-- read contexts asked and not given (`readreq`/`read`, B 657-667) -/
  reads : List (List w8) := []
  /-- the node runs (false from a restart's stop to its `boot`) -/
  alive : Bool := true
  -- today's drain fields, unchanged:
  qs : List Msg := []
  pend : List Msg := []
  xpend : List XMsg := []
  ce : List EntryM := []
  byE : AntCheck.Str := []
  cause : Option Msg := none
  told : Bool := false

/-- Today's `v.ps`, kept as a projection so that the S4 Sim proofs' text reads unchanged. -/
abbrev NodeView.ps (v : NodeView) : PState := v.r.p

/-- (new) The disk a node in sync mode, between inputs, has: its own state. -/
def durOf (r : RState) : DurW := ⟨r.p.term, r.p.vote, r.p.commit, r.full⟩
```

**The configuration history** is the log's (A3, `cfgFold`). The per-term records the binding keeps
(`ledConf`, `ledAt`, `elAt`) are related globally (§3.3, `LedConfOk`). The node holds only `conf`
and `confAt`. `conf` agrees with raft's applied configuration, with one exception: a restored
snapshot that is not yet applied, where the binding already switched (`ConfLag`, §6.3):

```lean
def ConfLag (dec : CCDec) (R : RunCfg) (v : NodeView) : Prop :=
  (v.conf = v.r.cfg ∧ v.confAt = lastConfIdx v.r.full v.r.cidx) ∨
  (v.r.snap = true ∧ ∃ cs, cfgFold dec R.c0 (v.r.fp) = some cs ∧ v.conf = cs ∧
     v.confAt = lastConfIdx v.r.fp v.r.fp.length)
```

`confView : CCState → AntCheck.Conf` (**new**) maps `incoming`/`outgoing` to sorted names. The
binding's `Conf` has no learners: `cin`, `cout` only (`Types.lean:163`). `lastConfIdx l k`
(**new**) is the index of the last conf entry among `l`'s first `k` (the binding's `LastConf`).

### 3.3 `AntSim` over N servers

`AntSim R S V net xnet` with `V : Fin R.N → NodeView` and `xnet : List XMsg`. The conjuncts of
today's `AntSim` are kept, each generalized as follows:

* `Shape`: `S.cfg = R.cfg`, every list of length `R.N`.
* `DurableIs` (C1) splits into **`DiskIs`**, the binding's term/vote/log/commit, which are `v.dur`'s
  (`S.log[n] = logOf v.dur.log`), and **`MemIs`**, `S.role[n] = roleS v` (`"precandidate"` if
  `v.pre`, else `roleOf v.r.p.role`, B 248-249), `S.lastApplied[n] = v.delivered.length`,
  `S.config[n] = confView v.conf` and `S.confAt[n] = v.confAt`. It adds **`SyncDisk`**:
  `R.md.async = false → v.mems = [] → v.Idle → v.dur = durOf v.r`. That is today's
  `S.currentTerm[n] = v.ps.term ∧ …`, through `durOf`. Also kept: `LogIdx v.dur.log`, the
  delivered prefix within the disk's commit, and `ConfLag`.
* **`UndoIs`** (new): `S.undo[n] = none ↔ v.undo = none`, and for `some p`: `p.made = v.made` and
  the pre-image `p.term, voteOf, p.commit`, with `(log.take p.keep) ++ p.suffix` equal to `v.undo`'s
  (B 349-359, what `boot` reverts to, B 170-181).
* **`QueueIs`** (new): `S.queue[n]` is `v.mems.map (evMem …)`, in order.
* **`ReadsIs`** (new): `(S.reads[n]).map (·.ctx) = v.reads.map hexOf`. Today's `BindingOk` conjunct
  `S.queue = [] ∧ S.reads = []` goes into `QueueIs`/`ReadsIs`.
* `LeaderPart`, `CandPart`, `PendOk`, `QsOk`, `LeadOk`, `VoteSelf`: `Fin 3 → Fin R.N`, `cfgM3` →
  `v.r.cfg.cfg`, `voters3` → the configuration's voters, and `base0` → `v.r.p.base` with the full
  log `v.r.full` wherever the binding's whole log is compared. `PendOk` gains arms for `.preVote`,
  `.preVoteResp`, `.readIndex`, `.readIndexResp`, `.snap` and `.propose` (forwarded, unchecked:
  B 524, 586). The `_ => False` arm stays, for types no Ready carries. `XPendOk` (new): an `XMsg` of
  the Ready is the node's (`src = id`, or a forwarded transfer) to a server.
* `BindingOk` (C3): `Fin R.N`. `LedConfOk` becomes
  `S.ledConf.get T = .ok (confView cs) ∧ cfgFold dec R.c0 (ledLog T).take (ledAt T) = some cs`,
  in place of `cfg3.initConf`. `ConfirmedOk`, `TermLenOk` and `TlSorted` are unchanged in text.
* `NetOk` (C4): `Fin R.N`. Its type disjunction gains `.preVote ∨ .preVoteResp ∨ .readIndex ∨
  .readIndexResp ∨ .snap`, and `.propose` keeps term 0 (`MsgShape`). `XNetOk xnet` (new): every
  `XMsg` sent is between two servers, of a term its sender reached. `HbCommitOk`, `NetShape` and
  `LeadCommitMsgOk` are unchanged in text. A heartbeat's `ctx` is unconstrained.
* `RaftFacts`/`RaftLaws`/`GlobalOk` (C5): `G.logs` hold full logs (`fp ++ log`, from index 1). Two
  fields are added: `G.snaps : List (Nat × List EntryM)`, the committed prefixes snapshots stand
  for (`raftSnapCert`), and `G.confs : List (List EntryM × CCState)`, the fold's admissible pairs
  (`Adm`). `GlobalOk`'s `n : Fin 3` becomes `Fin R.N`.

```lean
def AntSim (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
    (net : List Msg) (xnet : List XMsg) : Prop :=
  Shape R S ∧ BindingOk R dec S ∧ NetOk R S net ∧ XNetOk R S xnet ∧ ∀ n, NodeOk R dec S net n (V n)

def SimPre (R) (dec) (S) (V) (net) (xnet) (evs) (G) : Prop :=
  Prefix R.cfg evs S ∧ AntSim R dec S V net xnet ∧ RaftLaws G ∧ GlobalOk R S net G

def SimStep (R) (dec) (evs) (G) (ev : AntCheck.Event) (V' : Fin R.N → NodeView) (net' xnet') : Prop :=
  ∃ S', Prefix R.cfg (evs ++ [ev]) S' ∧ AntSim R dec S' V' net' xnet' ∧ GlobalOk R S' net' G
```

`dec` is the run's conf-change decoder, the harness's proposals' (§3.5, `confAgree`).

### 3.4 Inputs and reach

```lean
inductive Input where
  | recv (m : Msg) | recvX (x : XMsg)      -- RawNode.Step of a protocol / transfer message
  | tick | propose (data : List w8)
  | proposeConf (cc : ConfChangeIM)       -- ProposeConfChange (V1 or V2): an entry of type conf
  | readIndex (ctx : List w8) | campaign | transfer (to : w64)
  | snapStatus (to : w64) (ok : Bool) | unreachable (to : w64)
  | applyConf (k : Nat)                   -- ApplyConfChange of the entry at position k
  | storeAck (resp : List Msg)            -- async: a write's or apply's responses stepped

def Input.byE : Input → AntCheck.Str
  | .recv _ | .recvX _ => go!"recv" | .tick => go!"tick" | .propose _ | .proposeConf _ => go!"propose"
  | .readIndex _ => go!"read" | .campaign => go!"campaign" | .transfer _ => go!"transfer"
  | .snapStatus _ _ | .unreachable _ => go!"snapstatus" | .applyConf _ => go!"apply"
  | .storeAck _ => go!"write"

def InputStep (R) (dec) (Adm) (n : Fin R.N) (r : RState) : Input → RState → List XMsg → Prop
  | .recv m, r', xs => RecvEndR Adm (R.k n) (nodeId n) r m r' ∧ xs = []
  | .recvX x, r', xs => (x.ty = .timeoutNow ∧ TimeoutNowEndR (nodeId n) r x r' ∧ xs = []) ∨
                        (x.ty = .transferLeader ∧ TransferEndR (nodeId n) r x.src r' xs)
  | .tick, r', xs => TickEndR (R.k n) (nodeId n) r r' ∧ xs = []
  | .propose d, r', xs => RecvEndR Adm (R.k n) (nodeId n) r (propMsg (nodeId n) d) r' ∧ xs = []
  | .proposeConf cc, r', xs => RecvEndR Adm (R.k n) (nodeId n) r (propConfMsg (nodeId n) cc) r' ∧ xs = []
  | .readIndex c, r', xs => RecvEndR Adm (R.k n) (nodeId n) r (readMsg (nodeId n) c) r' ∧ xs = []
  | .campaign, r', xs => CampaignEndR (R.k n) (nodeId n) r r' ∧ xs = []
  | .transfer to, r', xs => TransferEndR (nodeId n) r to r' xs
  | .snapStatus to ok, r', xs => SnapStatusEndR (nodeId n) r to ok r' ∧ xs = []
  | .unreachable _, r', xs => r'.p = r.p ∧ r' = r ∧ xs = []
  | .applyConf k, r', xs => ApplyConfEndR dec Adm (R.k n) (nodeId n) r k r' [] ∧ xs = []
  | .storeAck resp, r', xs => StoreAckEndR Adm dec (R.k n) (nodeId n) r resp r' ∧ xs = []
```

`Reach`, `Quiet`, `ReadyD`, `ReadyOutP` and `Reported` keep their shape over `RState`.
`ReadyD` gains `pre : Bool`, `xmsgs : List XMsg` and `snap : Option entryID`. `ReadyOutP`'s
`ps.base = base0` becomes `md.snapshots = false → …`, and its log clause is restated on `r.full`.
`Reported` compares `roleS`, the reported string. In async mode `ReadyOutP` splits the outbox by
type, following `send` (`raft.go:546`):

```lean
def AfterAppTy (t : MsgType) : Prop := t = .appResp ∨ t = .voteResp ∨ t = .preVoteResp
```

`rd.msgs` holds the others, sent at once. The write's `Responses` hold the `AfterAppTy` ones. See
§6.1 for `MsgVote` (E1).

### 3.5 The statements, all 16 report kinds and boot after restart

Every statement has the shape

```lean
∀ R dec S V net xnet evs G n …, SimPre R dec S V net xnet evs G → <raft facts> →
  SimStep R dec evs G (<event as a function of raft data>) (setV V n v') net' xnet'
```

The table gives, per kind: the event function (`Abs.lean`, **new** unless stated), the view and
network after, and what it needs from raft. "Today" means the statement exists (`Sim/Stmts.lean`).
Today's statements are these at `R = R3` (`N = K = 3`, `boot = false`, `md = {}`).

| kind (B) | event | `v'`, `net'` | raft facts (premises) | batch |
|---|---|---|---|---|
| `boot`, fresh (162-194) | `evBoot R id` (voters `namesL R.K`; with `R.boot` term 1, commit 1, last index 1, last term 1: `BootInit`, B 733-753) | `v` | `PInitR R v.r` (the fresh or BootInit state, `restartP` at the written boot entry) | today, B1 for `R` |
| `boot`, after restart (162-194) | `evBootR R id d a cs` (term, vote, commit, last index/term of `d`; `applied a`; voters, outgoing of `cs`) | `NodeView.boot r0 d a cs` | `v.alive = false`; `d = v.dur ∨ (v.undo = some d ∧ v.made = false)`; `restartAtSpec`'s post: `r0 = restartR d a cs`, `cs` the fold of `d.log.take a` (`confAt γ a m`), `a ≤ d.commit` and `a` within `chain` | B2 |
| `recv` (199-204) | `evRecv id m` (today) | `told := true` | `m ∈ net`, `m.dst = id`, and, for a request, `Sendable` kept (C4) | today |
| `ready` (439-447) | `evReady id by roleS T V C es` plus `snap` (**new** field) | `afterReady` | `Reach`, `ReadyOutP`, `Reported`, `ReadyFacts`; `md.async = false` (else `mem`) | today, extended |
| `mem` (450-459) | `evMem id by roleS T V C first es w` | `w = 1`: `mems ++ [rec]`; role, `conf`, leader records moved | `Reach`, `ReadyOutP` at the in-memory state; `w = 1 ↔` the Ready has a write | B2 |
| `write` (462-470) | `evWrite id T V C first es` of `v.mems.head` | `dur := applied write`, `undo := some v.dur`, `made := false`, `mems := tail` | the write is the head's (storage goroutine's FIFO) | B2 |
| `wrote` (502-504) | `evWrote id` | `undo := none`, `made := true` | the write made, and its `Responses` released after | B2 |
| `flush` (474-478) | `evFlush id more` | `mems := tail`, the head folded into the next `net` | batch mode | B2 |
| `net` (483-492) | `evNet id T V C first es` | `undo := some v.dur`, `made := false`, `dur := ` the batch's write | batch write = union of flushed mems; `first` the lowest conflict (`ip + 1`) | B2 |
| `made` (496-499) | `evMade id` | `made := true` | the batch's write on disk | B2 |
| `send` (510-593) | `evSend id by m` and fields `b` (batch), `cause` (async) | `pend := rest`, `net ++ [m]`; `XMsg`: `xpend := rest`, `xnet ++ [x]` (`evSendX`, unmodelled, B 702) | `MsgFacts G q`; async: an `AfterAppTy` message only after `wrote`; a `MsgVote` only after its write (§6.1) | today, extended |
| `apply` (598-609) | `evApply id by ce` plus `a` (async) | `delivered ++ ce` | committed and written: `ce` within `v.dur.commit` | today |
| `conf` (614-630) | `evConf id k voters outgoing` | `conf := cs'`, `confAt := k` | `ApplyConfEndR` at `k`; `confAgree` (below); a leader's `recordedIn` (B 627: its commit covers `k`) | B3 |
| `restore` (634-643) | `evRestore id k voters outgoing` | `delivered := r.fp.take k`, `ConfLag` closed | `AckEndR`'s applySnap arm at `k`; `G.snaps` certifies `fp.take k` committed | B3 |
| `snap` (647-650) | `evSnap id k t` | `v` | `CreateSnapshot` at `k ≤ applied ≤ commit`, `t` the term at `k` of the full log | B3 |
| `readreq` (657-661) | `evReadReq id ctx` | `reads ++ [ctx]` | none (the driver's own context, unique per run) | B1 |
| `read` (663-667) | `evRead id ctx i` | `reads.erase ctx` | `rd.ReadStates` element `⟨i, ctx⟩` with `i ≥` the chain length at its `readreq` (raft's read-index safety: `ReadIndex.lean`'s `readStateRaw` gives `i` committed and at least the commit at request time) | B1 |
| `GC` (689-723) | none | `v` | today's `antSim_gc`, `Fin R.N` | today |

```lean
/-- The conf-change decoder of the run's entries (the harness is the only proposer: it marshals
every `ConfChange`/`ConfChangeV2` itself), with the binding's values: decoding then `ccStepB` is
`nextConf` of the reported value, and `legal` holds exactly when raft's `ccStepB` succeeds and the
leader's conf-change loop kept the entry. -/
abbrev confAgree.stmt (dec : CCDec) (valOf : EntryM → AntCheck.Value) : Prop :=
  ∀ (pre : List EntryM) (e : EntryM) (op : CCOp) (cs cs' : CCState),
    dec pre e = some (.apply op) → ccStepB op cs = some cs' →
    AntCheck.legal (confView cs) (valOf e) = .ok true ∧
    AntCheck.nextConf (confView cs) (valOf e) = .ok (confView cs')
```

`entOf` gains the conf arm: `type := "conf"`, `value := valOf e`, for `e.Type' ∈ {1, 2}`
(`EntryConfChange`, `EntryConfChangeV2`). `valOf` is the harness's `confValue`, built from the
`ConfChangeIM` it proposed, with no proto decoding in Lean beyond `CCDecodes` (`CCModel.lean:81`).
`msgShape.stmt`'s `EntsNormal` becomes `EntsHarness`: normal, or conf with `CCDecodes`.

**Restart's view.** `NodeView.boot r0 d a cs := { r := r0, delivered := r0.fp.take a ++ …, dur := d,
undo := none, made := true, mems := [], conf := cs, confAt := lastConfIdx d.log a, pre := false,
reads := [], alive := true }`. The binding's `Boot` clears `pending`, `queue`, `reads` and `undo`,
and sets `role := follower` (B 162-166).

### 3.6 Run-level statements

```lean
abbrev antSim_init.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (V : Fin R.N → NodeView),
    (∀ n, PInitR R (V n).r ∧ (V n).Idle ∧ (V n).alive = false ∧ (V n).dur = durOf (V n).r ∧ …) →
    ∃ S, Prefix R.cfg [] S ∧ AntSim R dec S V [] [] ∧
      ∀ G : RaftFacts, bootLog R ∈ G.logs → GlobalOk R S [] G
```

`bootLog R` is `[]`, or `[⟨1, 1, EntryConfChange?…⟩]` per `BootInit`. The driver helper's
`bootStorage` writes their single boot entry: B 742 pins its value. The closed theorem quantifies
over the `RunCfg` the program draws (`Main`'s `below`, under the mask). No premise names a mode.

## 4. The RawNode API surface the driver calls

Each spec keeps today's `form R S` pattern (`RawNodeAbsSpecs.lean`). The changes: `R` takes
`r : RState` and the scope `Option RnMode`, and `S : RnMode → Prop` is `fun md => sc = some md`.
The guarded post is `"%Hend" ∷ ⌜∀ md, S md → End …⌝`. `rnCfg γ` disappears, since the configuration
is `r.cfg.cfg`. New forms:

| function | input message / effect | post `End` | premises in scope (`S md`) | batch |
|---|---|---|---|---|
| `Step` | as today, at `stepTypes md` | `RecvEndR`, `TimeoutNowEndR`/`TransferEndR` (an `XMsg` result: the Ready's `xmsgs`), `StoreAckEndR` | the type in `stepTypes md`; `MsgProp` with `fwdP` resources (forwarding) | B1-B3 |
| `Tick` | today | `TickEndR` | none | today |
| `Propose` | today | `RecvEndR … (propMsg …)` | none | today |
| `ProposeConfChange(cc)` | `MsgProp` of one conf entry (`rawnode.go:120`, `ConfChangeToMsg`) | `RecvEndR … (propConfMsg id cc)` | `confChanges`; `cc` not E4's shape (`ccWellFormed`) | B3 |
| `ApplyConfChange(cc)` | `applyConfChange` + `switchToConfig` | `ApplyConfEndR` at the next conf position, returns the `ConfState` (`confStateIs csm cs'.cfg`) | the entry at `k` the one handed out (`delivered[k] = e`, `dec … = .apply op`) | B3 |
| `ReadIndex(rctx)` | local `MsgReadIndex` (`Entries: [{Data: rctx}]`) | `RecvEndR … (readMsg id rctx)`; later `Ready.ReadStates` give `⟨i, rctx⟩` with `readStateRaw` | `reads`; `rdCred γ 1` | B1 |
| `TransferLeader(to)` | local `MsgTransferLeader` | `TransferEndR` | `transfer` | B1 |
| `Campaign()` | `MsgHup` | `CampaignEndR` | none | B1 |
| `ReportUnreachable(to)` | `MsgUnreachable` | `r' = r` | none | B1 |
| `ReportSnapshot(to, st)` | `MsgSnapStatus` | `SnapStatusEndR` | `snapshots` | B3 |
| `HasReady` | today | `PIdle` over `r` (role via `roleProto`: pre-candidate as follower) | none | today |
| `Ready` | today | `ReadyOut` with `xmsgs`, `snap`, and in async mode the split by `AfterAppTy` and the storage messages' fields | `md.async` decides the split | B2 |
| `Advance` | today (sync only) | `AdvanceEndR` | sync | today |
| `NewRawNode` fresh/boot | `emptyStartForm` | `r = rInit R` | `RunCfg.boot` decides `bootLen ∈ {0, 1}` | B1 |
| `NewRawNode` restart | `restartAtSpec (some md)` | `r = restartR d a cs`, nothing queued, `ip` the stored log's end | `storage` the durable part (`StorageHolds S σ`) | B2 |

`PIdle`'s `roleGo ps.role = rs.role` becomes `roleProto rs.role = r.p.role`
(`roleProto StatePreCandidate = .follower`). This is a weakening, and the old proof gives it
through `roleProto ∘ roleGo = id`.

**The vacate law (B2).** The restart is in-process. No `crashed` token is available, so this is not
`nodeCrash` (`InvNodeRule.lean:745`). It is `node.Stop`'s RawNode counterpart: a `RawNode` dropped by
its only owner gives back the id's vacancy. Its durable state is what the batches it entered left
(`ownDurGhost`). An announced-but-unentered batch is discarded, which is the binding's undo of an
unmade write.

```lean
abbrev ownRawNodeAt_vacate.law : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg)
    (ip : Nat) (sc : Option RnMode) (x : CrashNames) (g : Nat) (S : RaftState) (E : CoPset),
    ↑N ⊆ E →
    isCluster γ N -∗ ownRawNodeAt γ.raftNames rn id rs r qs ip sc -∗
      genView γ.raftNames id x 1 g -∗ raftState γ id S ={E}=∗
      ∃ x', nodeVacantA γ id x' ∗ raftState γ id (durRaftState rs) ∗
        ⌜StorageHolds (durRaftState rs) (durContents rs)⌝
```

`durRaftState rs` and `durContents rs` (**new**, raft side, B2) read `rs.dur`, the client-entered
durable maps, as `restartAtSpec`'s `S` and `σ`. Soundness check for B2 before proving: a `Ready`'s
`Henter` taken after the vacate is impossible, because the wand needs `ownDurGhost` and `genView`
(consumed). Messages of the old generation in flight stay valid: their facts are persistent
(`isMessage`). The harness's storage wrapper keeps the durable part. kvdurable's `restartStorage`
is the pattern.

**Async storage writes (B2).** The storage goroutine receives `MsgStorageAppend` /
`MsgStorageApply` (`Ready.Messages` to `LocalAppendThread`/`LocalApplyThread`). It writes, then
steps the `Responses` back on the node goroutine. The specs: `Ready.form`'s post at `md.async` says
the local messages' fields are the write (`HardState`, `Entries` from `ip + 1`, `Snapshot`) and
`Responses = outbox.filter AfterAppTy ++ [selfResp]`. `Step.form` at `MsgStorageAppendResp`/
`ApplyResp` gives `StoreAckEndR`. The storage write itself is `MemoryStorage`'s proved
`Append`/`SetHardState`/`ApplySnapshot` (13 ops, plan §0).

## 5. Migration and re-proof cost

| existing statement | change | how the proof adapts | cost (helper-rounds) |
|---|---|---|---|
| `InputEnd.lean`: `PreEnd`, `RecvEnd`, `HandleEnd`, `TickEnd`, `AdvanceEnd` | `k` argument; new disjuncts/arms; `AppSendOk → SendOk`; heartbeat `ctx = [] → hbCtx` | `Or.inl`/same match arm; `hbCtx_nil` rewrite under `ro.pending = []` | in `InputEndLift`'s cost |
| `InputEndLift.lean` (~25 lemmas) | `LiftScope k c id s` takes `k := ⟨s.prevote, s.cq, s.sdr⟩`; the `prevote = false ∧ cq = false` conjuncts stay for the old lemmas | mechanical: new arms are new disjuncts, old lemmas produce old ones | 0.5 |
| `RawNodeAt.lean`: `RnScope`, `RnCfgIn`, `rnScopeAt`, `ownRawNodeAt` | `Option RnMode`; `toRState`; `Hasync` guarded | `RnScope {} ↔` today's (by `simp`); `ownRawNodeAt_ownRawNode` unchanged in proof | 0.5 |
| `RawNodeAbsSpecs.lean` forms (6 + start) | `R` over `RState`; `rnCfg γ → r.cfg.cfg`; `S md`; ends `…R` | the `wp_absProof`s (in `RawNode__*Abs.lean`, ~2.5k lines): `RecvEndR` = `RecvEnd ∧ bookkeeping` (bookkeeping from the unchanged `NState` fields); `rnCfg γ = r.cfg.cfg` from `RnCfgIn {}` | 1.5 |
| `RawNodeStart.lean` `restartAtSpec sc` | `sc : Option RnMode`; the `sc = true →` block conditioned per flag | mechanical | 0.3 |
| `Sim/Abs.lean` | `cfg3 → R.cfg`, `nodeId` over `Fin N`, `roleOf` + precandidate, `entOf` conf arm, new `ev*` | new defs; `cfg3 = R3.cfg` | 0.3 |
| `Sim/Rel.lean`, `Stmts.lean`, `MsgShapeStmt.lean` | §3 | restated (the only real restatement, paid once) | lead, 1 |
| `Sim/*.lean` proofs (~12.4k lines, 28 files) | `Fin 3 → Fin R.N`, `cfgM3 → v.r.cfg.cfg` (with `md.confChanges = false`: `= CfgM.simple voters0 ∅`), `v.ps` kept as an abbrev, `DurableIs → DiskIs ∧ MemIs ∧ SyncDisk` | mostly mechanical; `DiskIs` through `SyncDisk` (`v.dur = durOf v.r`) one rewrite per use; `base0 → v.r.p.base` with `md.snapshots = false` | 2.5 |
| harness proofs (~11k lines, 45 files naming `Fin 3`/`cfg3`/`nodeId`/`voters3`) | N servers, `RunCfg` drawn, the new driver's goroutines | the `Fin 3` part mechanical (1.5); the new goroutines are B1-B4's new work, not migration | 1.5 |
| top level (`TopLevelRobustness`, `Results`) | `raft_antithesis_accepts` at `R.cfg`; `_basic` kept by mask `{}` | restated | 0.3 |

**Total migration ≈ 8 helper-rounds, paid once at B1's start.** The B1 estimate (12-14) already
includes the N-server generalization (P4). The rest of the migration (the RState wrapper, mode
record, statement restatement) is ≈ 3 rounds of it.

## 6. Risks: where a final-scope statement might be false

### 6.1 E1: async vote requests (checked: **the fork lacks the patch**)

`raft.send` holds only `MsgAppResp`, `MsgVoteResp` and `MsgPreVoteResp` for the write
(`raft.go:546`, fork `d2c16c5`). `MsgVote` goes to `r.msgs` at once. Their patch
(`antithesis-fm/patches/README.md`, E1; etcd-io/raft#551) adds `MsgVote`. Their rawnode holds vote
requests by default (`rawnode/node.go:175-180`, `NoHoldVote`). Unheld, the binding rejects at the
first vote request, and that is a real upstream safety bug (their `repro/asyncvote`).

* **Statement consequence:** in async mode the Sim's `send` of a `MsgVote` requires `v.made` at its
  campaign's write. `ReadyOutP` (async) puts `MsgVote` in `rd.msgs` (raft's truth). So the hold has
  to be the driver's: a vote request is sent at `wrote`, as their rawnode does.
* **Recommendation:** the driver holds vote requests (parity with their harness, and the
  application's choice under raft's documented contract). Patching the fork with E1 is a raft
  change needing re-proof of `send`, so it is not a B2 item. **Open question for Upamanyu:**
  report E1 against our fork as a known upstream issue (with `repro/asyncvote` ported), or not.

### 6.2 E3: split writes plus membership (the fork lacks the patch)

`hasUnappliedConfChanges` scans only up to `committed` (`raft.go:1013-1037`). With entries written
before the HardState and a crash between, a node keeps the second change, loses the commit covering
the first, and campaigns with a two-changes-old configuration (their E3). The README order
"entries, then HardState" is already excluded as a model limitation (plan §2, `splitEH`). The
driver's split orders are only the ones their model accepts (`term-entries-commit`,
`hardstate-entries`). E3 then needs a lost commit with a kept entry, which those orders cannot
produce.

**Check in B2:** `hardstate-entries` persists the commit before the entries. That can make a
commit index past the durable log's end. Does raft's restart accept it (`restartAtSpec`'s
`a ≤ σ.commit`, `γ.bootLen ≤ σ.commit`)? Their binding's `undo` (B 349-359) is per announced write,
so a split write is several announced writes, and `boot`'s `Recovered` must match one of them.

### 6.3 Snapshot configuration: receipt vs apply (expected finding, B3)

Their model switches at receipt (B 258-260: `config := ConfOf(chain, snap.index)` at the `ready`
with `snap`, R 474-483 `RestoreConf`). The fork switches at apply (`StepR.applySnap`,
`StepR.lean:430`; the fork's fix of `issues/raft-snapshot-during-apply-stale-confchange.md`). `ConfLag`
(§3.2) states the window. **In sync mode it is unobservable:** between the `ready` with `snap` and
`restore` the drain takes no input, and the only reports are the Ready's `send`s, whose binding
checks read no configuration. **With async + snapshots + membership** the node steps inputs in the
window. raft campaigns or tallies with the old configuration, where the binding expects the new one.
That can be rejected at `wins` (`isQuorum(granted, config[n])`, B 238), flagged `Unpromotable`
(B 274), or rejected at `conf` (B 616: `k > confAt[n]`, where the binding's `confAt` already jumped
past an entry raft still applies). Statement consequence: `antSim_ready`/`antSim_conf` under
`md.async ∧ md.snapshots ∧ md.confChanges` carry `ConfLag`'s left disjunct as a premise. A run that
violates it is the finding, reported with a Go reproducer per decision 5. Never weakened.

### 6.4 `MsgTimeoutNow` raising the term by more than one (B 366-367)

`elect ⇒ T1 = T0 + 1`. A `MsgTimeoutNow` at term `m.term > T0` would give
`T1 = m.term + 1 > T0 + 1`. This is unreachable in our runs: the leader sends it to `to` only when
`Match[to] = lastIndex` (`raft.go:1475, 1530`). That `Match` came from `to`'s acknowledgement at the
leader's term `T` (`reset` zeroes peers' `Match`), so `to`'s durable term is `≥ T = m.term`. A
duplicate after the campaign is stale. **Proof obligation (B1):** a Sim invariant
`XNetOk`: `x.ty = .timeoutNow → S.currentTerm[x.dst] ≥ x.term`, established at the `sendX` from
`LeaderPart`'s ack and `AckTermsOk`.

### 6.5 Network duplication and a forwarded `MsgProp`'s tickets (decided)

**Decision: run the harness's cluster in raft's existing `dup` mode (`RaftNames.dup = true`).**
Its proposal tickets are persistent, so every copy of a forwarded `MsgProp` carries them and each
copy may be appended. Reason: the mode exists and is proved, kvdurable already uses it for its
duplicating network, and it allows the real execution (a duplicated proposal appended twice).

The mechanism, checked in code:

* `propTk` (`raft/Protocol/Ghost.lean:1222`) is `dghostVar γt (if γ.dup then DFrac.discard else
  DFrac.own 1) none`. In a `dup` cluster it is persistent (`propTk_persist`), and `propTk_set` keeps
  it while giving `propIdx γ d i` for every index a copy is appended at (`propIdx`'s `dup`
  disjunct).
* `msgCredits_copy` (`raft/InvNode.lean:1615`) gives `□ msgCredits` of any message in a `dup`
  cluster. That covers `stTks`, the entries' `entTk`s (`ApiVocab.lean:531`).
* The client's update is `□?γ.dup` in `rawNode_prop_mint` (`RawNodeStartSpec.lean:136`) and in
  `GhostState.lean:1162`: firing a persistent `propAu1` leaves it in place.
* The client log is `firstOcc`, so a repeated datum adds nothing.
* kvdurable does exactly this (`kvdurable/Cluster__deliver.lean:7-9, 93`: "a duplicate is a fresh
  copy … `γ.dup = true`").

**Rejected alternatives:**

* *A duplicate carries no tickets, and `Step` on a ticketless `MsgProp` gives only the non-ticket
  post.* False for raft's invariant. Every non-filler log entry needs `entDataIs γ e (some d)`, which
  needs `propIdx γ d e.Index'` (`Ghost.lean:1287-1290`). Outside `dup` mode `propIdx` comes only from
  consuming a ticket, so a leader appending a ticketless copy cannot keep the log invariant. Real
  raft does append it.
* *Network duplication excluding `MsgProp`.* This is harness steering, which plan §4 decision 3
  forbids, and it is unnecessary given `dup` mode.

**What it costs, in B1:**

* `PropMint.propOk_mint` (`ant/PropMint.lean:107`) takes `Hdup : γ.raft.dup = false`. It changes
  to the persistent update: `□ AU` from `ops_au` (`PropMint.lean:72`), whose only hypothesis
  `opsInv` is persistent.
* The harness's cluster allocation sets `dup := true`.
* Every proof that used ticket exclusivity at the harness level is checked. Expected: none, because
  the binding has no uniqueness check.

**A related B1 item, not a decision:** a duplicated `MsgReadIndex` needs one more `rdCred γ 1` per
copy (`RawNode.Step`'s `"Hcred"`, a separate premise from `msgCredits`). The credits come from the
cluster's receipt pool (`InvApiDecAlloc.lean:100`, `⧗ k ∗ rdCred γ c`). The network goroutine that
duplicates must obtain the credit there, which needs a law (`rdCred` from `⧗ 1`) if raft's API does
not already export one.

### 6.5a Forwarding (#44) on top of the `raft.Step` widening

The `raft.Step.spec` premise widening for `MsgProp` (`Term = 0`, any `From`; zeldovich-proving-3,
landing on `lean` on its own) is taken as given. B1 does not re-prove `raft.Step`. B1 needs these
four things from the widened spec:

1. The premise admits a network `MsgProp`: `Term = 0`, `From` a peer (`From ≠ id`), its credits
   `msgCredits` (the tickets `stTks`, copyable under `dup`), and the entries' `propData`.
2. `StepEnd` keeps the `MsgProp` arm it has today (`StepEndTy` includes `MsgProp`). A leader
   appends, consuming or (under `dup`) keeping the tickets, `propIdx` at the stamped indices. A
   follower with a leader forwards with `From` kept (`send` sets `From` only when it is `None`,
   `raft.go:515-517`) and the tickets travelling in the outbox (`msgsTks`). Otherwise the proposal
   is dropped (`ErrProposalDropped`).
3. The forwarded copy's facts are in the `Ready`'s messages (`isRaftMsg`), so the harness can send
   it on.
4. The term ceiling is trivial at term 0.

On the RawNode/InputEnd side (joint with them, after antithesis-s4 lands):

* `ProposeEnd`'s forward arm keeps the sender: `Msg.mkV .propose m.src s.lead (W64 0) …` in place
  of `… id …` (`InputEnd.lean:155`). This is a statement change. The local `Propose` proof adapts
  by `m.src = id`, since `propMsg` has `From := id`.
* `RawNode.Step.form` admits `MsgProp` at `md.forwarding` (`stepTypes`), with `NetMsgOk` relaxed to
  `Term = 0` for that type.
* The Sim's `Reach.input` drops `m.term ≠ 0` for `m.ty = .propose`, which routes to `RecvEnd`'s
  local arm (`m.term = 0 ∧ HandleEnd`).
* `PendOk`'s and `NetOk`'s `.propose` arms are already in place (unchecked by the binding, B 524,
  586).

### 6.6 Smaller risks

* **Pre-vote:** the binding accepts `"precandidate"` (B 244) and treats it as a follower. The
  `preVoteResp` arm (R1) is sound because the binding accepts any follower's campaign to `T0 + 1`
  with its own vote (B 367). The remaining check is `Unpromotable` against `config[n]`, which is
  raft's `promotable` at the same configuration (§6.3 aside).
* **CheckQuorum step-down:** a leader becoming a follower at its own term passes B 365
  (`T1 = T0`). The binding's `leaders` keeps the record and GC drops it later (B 709). Low risk.
* **Non-voters (`K < N`):** a node outside its configuration with no `Progress` for itself.
  `LiftScope`'s `id ∈ domSet prvals` must be weakened to `FnScope`'s form (only a non-follower,
  which such a node never is: `promotable`). Raft side, B1, low risk.
* **BootInit (`R.boot`):** `RawNode.Bootstrap`'s entries fit neither initial state (plan §2,
  B 155-157). The driver writes their boot entry into storage, which requires `restartAtSpec` at
  `bootLen = 1`, an existing case (`γ.bootLen ≤ σ.commit`). Low risk.
* **Inflight, message size:** the specs are generic (`MaxInflightMsgs < 2^62`,
  `MaxSizePerMsg ≤ entsCutMax` under `maxData`). Check that `entsCutMax` admits their sizes (B1).
* **Auto-leave** (`appliedTo` proposing an empty `ConfChangeV2`) produces a leader append with
  `by = "apply"`, which `ok` (B 233) accepts. `AckScope`'s `autoLeave = false` premise goes (B3).
  The auto-leave V2 has `Transition = Auto`, so it is not E4's shape.

### 6.7 Plan §2(c) divergences, summary

| divergence | where | statement handling |
|---|---|---|
| snapshot config at receipt vs apply | §6.3 | `ConfLag`; a finding if hit (async + snap + member) |
| E1 vote request before write (fork unpatched) | §6.1 | driver holds `MsgVote` until `wrote`; Sim `send` premise |
| README split order (entries, then HardState) | §6.2 | not exercised; a documented model limitation |
| several async writes made as one (B 462-470) | plan §2 | the storage goroutine makes writes one at a time (FIFO); `write` per `MemRec` |
| `MsgTimeoutNow` term jump (B 366) | §6.4 | unreachable; `XNetOk` invariant |
| lease reads (`ReadOnlyLeaseBased`) | plan §2 | not modelled; `ReadOnlyOption' = 0` stays a premise |
| logs whole in their model | §1.1 | `r.full`, `G.snaps` |
| duplication vs tickets | §6.5 | raft's `dup` mode (persistent tickets), as kvdurable |

## 7. Open questions (each with a recommendation)

1. **E1 report** (§6.1): report it against the fork as an upstream issue with a Go reproducer.
   Recommend yes, as an issue only, no fork patch now.
2. **Duplication** (§6.5): decided, `dup` mode. Open only: the read-credit law for duplicated
   `MsgReadIndex`, if raft's API lacks one.
3. **`Fin R.N` with `N ≤ 9`**: recommend yes. Their cfgs use 3 and 5.
4. **`XMsg` outside `Msg`** (§1.3): recommend yes. It keeps raft's message invariant untouched.
5. **Nondeterministic arms (R1)**: recommend yes. No binding check needs the hidden state (lease,
   pre-candidate tally, `recentActive`, `leadTransferee`).
6. **Cleanup: a pure module for what Sim needs** (B1, accepted for now). `CCState` lives in
   `InvConfchange.lean`, whose imports reach `InvTracker` (Iris definitions); the Sim imports it
   through `Protocol/StepR.lean` (and `InputEnd` once it imports `StepR`). Move `CCState` and the rest
   of what the Sim reads (`cfgFlags`, `ccStepB`, `cfgFold`) into a pure module, so that the Sim
   imports no Iris.
