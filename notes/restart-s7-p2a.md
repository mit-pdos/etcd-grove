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
