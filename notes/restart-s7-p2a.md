# Restart S7.3 (P2-a): the single-voter "no `MsgSnap`" law, Go check and design (2026-11-14)

The law etcd-grove-81 approved at CP-b (`notes/restart-s7-probe.md`, "Decided"), narrowed: **a `MsgSnap`'s
destination is in the sender's tracked progress set (its configuration's voters and learners) at send
time, and is not the sender.** No clause on the sender's membership (a leader that removed itself stays
leader for a while in raft v3). With static one-member membership the two facts exclude every `MsgSnap`,
so `srvRestartRows` (row 4 `rnSnapTermAbove` and `srvWinPend`) holds vacuously for `restart1`.

## The Go check (done)

At the raft fork's pin (`565c2bd`, `upamanyus/etcd` branch `raft37-goose-lean-a2`), in a scratch clone
(`/shared/tmp/restart-s7/raft-check`, patch `/shared/tmp/restart-s7/p2a-check.patch`): `send` panics when
a `MsgSnap`'s `To` is not a key of `r.trk.Progress`, and counts the `MsgSnap`s it checks. Raft's whole
package test suite (unit, paper, flow-control, snapshot, the data-driven interaction tests, `rafttest`)
passes under the 32G cap with GOWORK=off: **16 `MsgSnap`s sent, none to an untracked id.**

By reading, the same holds of every path:
- `maybeSendSnapshot(to, pr)` has one caller, `maybeSendAppend(to, …)`, which starts with
  `pr := r.trk.Progress[to]` and calls `pr.IsPaused()`: a `to` outside the tracker would be a nil
  dereference before any send. Its callers (`sendAppend`, `bcastAppend`, `stepLeader`'s
  `MsgAppResp`/`MsgHeartbeatResp`/`MsgSnapStatus` arms behind `pr == nil` returns, the transfer arm, the
  conf-change arm iterating the tracker) all pass a tracked id.
- `send` panics on a non-response message addressed to `r.id` (`message should not be self-addressed`):
  the "not the sender" half, about the sending node's id, not the message's `From` field.
- The tracker's keys are its configuration's voters and learners (`confchange`'s `checkInvariants`), and
  the tracker changes only in `applyConfChange` (fed by the application) and `restore` (a snapshot).

## The uncommitted-entries question: does not arise

The tracker's configuration changes only through `ApplyConfChange`, whose dynamic-mode premise in the
raft API (`Spec/go_etcd_io/raft/v3/RawNode__ApplyConfChange.lean`, `DynCCPre`) is "the next **committed**
conf entry's decoded change", and through `restore` of a snapshot, whose configuration is certified
(`raftSnapCert`: the fold of the recorded decisions over a full log prefix ending at the snapshot). So
the sender's configuration at send time is the fold over a committed prefix, and the server's static
membership (`srv_confAt_eq_simple`: every committed configuration is the boot one) applies to it. A
leader's uncommitted conf entries do not reach the tracker in raft v3 (the application applies conf
changes after commit).

## The law's form (design; to be proved)

- **Where.** Raft's API, in `isRaftMsg γ id st` (`Proof/go_etcd_io/raft/v3/ApiVocab.lean`), which already
  carries the sender `id` (`AppFrom id st`): a new clause
  `□ (⌜st.msg.Type' = MsgSnap⌝ -∗ ⌜st.msg.To' ≠ id⌝ ∗ snapToTracked γ id st.msg.To')`, with
  `snapToTracked γ id d`: statically `TrackedOk`'s bound (as the protocol's `.snap` clause); dynamically
  some committed full prefix `fp` and recorded decisions `M` (`decLb γ M`) whose fold is a configuration
  `c` (`D.fold M fp = some c`) with `d ∈ c.voters ∪ c.learners`. (The protocol's `.snap` clause states
  `m.dst ≠ m.src`, about the `From` field, which raft's API does not tie to the sender for a `MsgSnap`;
  the API-level clause about `id` is the one `srvWinPend`, keyed by member id, needs.)
- **Sender side.** `raft__Step`'s `maybeSendSnapshot` path: the tracker's keys as its configuration
  (the static path already carries `TrackedOk` from `InvRawnode`'s tracker row, `domSet s.progress`);
  dynamically, the node's configuration as the decisions' fold over its committed prefix (what
  `ApplyConfChange`'s `DynCCPre` and `restore`'s certificate maintain), carried to the `Ready`'s
  `isRaftMsg` (`InvRawnodeReady`).
- **Receiver side.** Nothing destructures the new clause but its users; existing destructurings of
  `isRaftMsg` gain one pattern.
- **Server side.** `srvRestartRows_single : γ.vs = [id] → ⊢ srvRestartRows γ id A σ`: every committed
  configuration is `simple {id}` (`srv_confAt_eq_simple`, after relating raft's decision fold to the
  server's `confAt`), so a `MsgSnap`'s `To` is `id`, against `To ≠ id`; both rows' bodies then hold
  vacuously.
- **Interface.** `interface/` diffs of raft's API (`etc/api/raft.txt`: `ApiVocab`, `Api`); a hard stop
  for etcd-grove-81's review before landing.

Est. 1.5-2.5 wk (raft side 1-1.5 wk, server side 0.5-1 wk).

## Approved (etcd-grove-81, 2026-11-14), and where the proof stands

The design is approved: the clause goes in `isRaftMsg γ id st`, proved raft-side over `InvNode` as a law of
the API module (nothing unsealed), then `srvRestartRows_single`; hard stop at the `ApiVocab`/`Api` interface
diff.

Mapped so far (no code yet):
- **`To ≠ id` is already maintained**: the raft struct's queue invariant carries "not self-addressed (`send`'s
  panic)" for every queued message (`InvRaftPhys.lean`, `ownRaftPhysC_msgs`'s `⌜st'.msg.To' ≠ id⌝`, durability
  stage II (m)). It has to be carried to the `Ready`'s messages (`outboxRelP_isRaftMsg`/`_gen` in
  `InvRawnodeReady.lean`, which build `isRaftMsg` from `XfOk`'s clauses: add the clause to `XfOk` or pass
  it beside `Hsh`/`Hfr`).
- **The tracked half** is the bulk: `maybeSendSnapshot`'s `to` is a key of `r.trk.Progress`
  (`maybeSendAppend` reads `Progress[to]`); the static path already turns the tracker's keys into
  `TrackedOk` (`InvRawnode.lean:2735`, `domSet s.progress`); the dynamic path needs the tracker's
  configuration as the decisions' fold over a committed prefix (`StepGhostMode.lean:399`'s dynamic case,
  `ApplyConfChange`'s `DynCCPre`, `restore`'s `raftSnapCert`), carried into the queued message's facts.
- Producers of `isRaftMsg` to update: `outboxRelP_isRaftMsg`, `outboxRelP_isRaftMsg_gen`
  (`InvRawnodeReady.lean`), `InvApiView.lean:432`; destructurings: `InvApiView.lean:395`,
  `isRaftMsg_isMessage`, `isRaftMsg_dat`, `NetMsgOk`, `InvNode`/`InvApi`'s `sentMsg` laws.

## Progress and a finding (2026-11-14, hard stop for etcd-grove-81)

**Done (branch `restart-s7`, raft builds through its `Link`):** the protocol carries the destination fact.
- `Protocol/GhostState.lean`: `snapDstOk γ d` (statically nothing; dynamically `d` a voter or learner of a
  configuration `CfgAt γ M L c` of a committed log `L`), `cfgCommitted γ c`, `snapDstOk_of_cfg`; the `.snap`
  clause of `isMessage` gains `snapDstOk γ m.dst`.
- `Protocol/StepR.lean`: `StepR.win`/`sendApps` carry the snapshot destination fact (`StepC`'s, which the
  dynamic model dropped); producers `MsgVoteResp`, `MsgProp`, `StepCF.toR` supply it from `ReplSends`'
  `domSet s.progress` fact; consumers `RefinementDyn`, `StepRInv` take it.
- `Protocol/StepGhost.lean`: `cfgCommitted_of_env` (the step's configuration is a committed log's, from
  `dynEnv` and the node's committed prefix); `replOk_message` takes the configuration's commitment and the
  destination fact and gives the new conjunct. `Refinement.lean`'s `win`/`send_apps` pass them; `SnapMint`'s
  re-content keeps the conjunct.

**Finding: row 4 (`rnSnapTermAbove`) cannot be discharged from `isRaftMsg`.** Row 1 (`srvWinPend`) reads
`sentMsg` (which carries `isRaftMsg`, hence `isMessageC` of the `MsgSnap`'s abstraction, hence `snapDstOk`), so
it follows from the clause plus `To ≠ id`. But row 4 is a fact at the **receive of a `Ready`** (`readyRest`),
and a `Ready`'s messages carry `isRaftMsg` only behind the batch's durable fragments
(`readyPost`: `□ (durFrags … -∗ isRaftMsg …)`, or at role leader), because the outbox keeps a pending
message's `isMessage` behind `durFrags` (`outMsgOk`). `readyRest` itself carries no message facts
(`msgOutU`, `msgCredits`). So the destination fact is not available where row 4 is used
(`rnRestartOk_snapTerm`, `InvRaftNode.lean`).

**Options:**
- (A) *Recommended.* Keep the destination fact outside the durability wand: `outMsgOk` gains, unconditionally,
  `□ (⌜m.ty = .snap⌝ -∗ snapDstOk γ m.dst)` (it reads only committed state), and `readyRest` gains per message
  `□ (⌜q.st.msg.Type' = MsgSnap⌝ -∗ ⌜q.st.msg.To' ≠ id⌝ ∗ snapDstOk γ.raft q.st.msg.To')` (raft API: `readyRest`
  is in `InvApi`/`InvNode`). Then both rows follow for one member. Est. +1 wk over the approved design.
- (B) Prove `rnSnapTermAbove` in general (R2d'b: a raft-struct invariant that messages queued since the
  restart are above `t0`, and a `StartNode` post change), 5-8 d est.; it serves R2s-A too. Row 1 still needs
  the approved clause.
- (C) Not acceptable: carrying row 4 into the closed theorem.
