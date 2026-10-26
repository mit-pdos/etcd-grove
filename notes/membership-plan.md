# Membership changes in the server (track T-M, D21d (B)) — plan

Planned 2026-10-25. Status: **M2b, M2c done** (pre-vote and `StepDownOnRemoval` off in the dynamic mode, 2026-10-25); **M0 in part**: Q1-Q4 decided (D43: removal only; pre-vote and
`StepDownOnRemoval = false` proved in the dynamic mode; the removed member's own stop); W3 settled
(the user for the D22 owner: the peers right is `trLive`, D43); the example and the client path
still open.

## Goal

Today etcd's server runs raft in the **static mode**: the members are the bootstrap ones for good.
`srvCCPolicy` (`InvRequest.lean:285`) admits only the bootstrap `AddNode` entries,
`EtcdServer.applyConfChange` is an axiom over them (`ccApplyOk`: an `AddNode` of a known member,
`removed = false`), `IsIDRemoved` is proved `false`, `apply`'s `shouldStop = false`, `run` never
returns (its `stop` and `errorc` bags carry `False`), and `NewServer` freezes the transport after
`Start` (`trFrozen`: no `AddPeer`/`RemovePeer` after it). Every server-based closed theorem
(`linkv3p_safe`, `putget3_safe`, ...) is over that fixed member set (`bootPremise`: `γ.reDyn =
none`).

The goal: a closed theorem in which **the cluster's membership changes at run time** -- a member
removed (first), later one added -- with the KV store's safety unchanged, the server running raft
in the **dynamic mode** that raft's proof already has (reconfiguration stages A-B8, N;
`notes/reconfiguration-safety.md`). What becomes proved rather than excluded: `applyConfChange` for
the change kinds in scope, the membership writers, `RemovePeer`, the removed member's stop, and the
`errMemberRemoved` paths that are unreachable today.

## What exists (the inventory, 2026-10-25)

**Raft (proved, either mode).** `RawNode`/`node` in the static and the dynamic mode (B7c, N),
`ApplyConfChange` and `ProposeConfChange` in both (`wp_applyConf_dyn`), snapshots carrying a
configuration (B8), the read index (B6). The dynamic mode's limits, which etcd's server meets
**not** as configured:
- *Pre-vote off in the dynamic mode* (`ownRawNode`'s `Hpvoff`, status-history "Stage P"): pre-vote
  in the dynamic mode needs `RInv` to keep `StepR.campaign`'s guard for a pre-candidate
  (`notes/reconfiguration-safety.md` 4.1). **etcd's default is `PreVote: true`**
  (`embed/config.go:544`; `bootstrap.go:573` passes `cfg.PreVote`).
- *`StepDownOnRemoval` on in the dynamic mode* (`sdrOk`, B7c-2). **etcd's server does not set it**
  (Go's default `false`).
- *Start*: `Bootstrap`/`StartNode` are static-only (`Spec/.../StartNode.lean:23`); the dynamic mode
  has only `RestartNode` on empty storage. The server starts a new cluster with `StartNode`.
- etcd proposes only v1 `ConfChange`s (`configure`), so simple configurations: no joint state, no
  auto-leave (the dynamic mode's "no auto-leave joint" holds).

**The server.**

| Go | Lean today |
|---|---|
| `EtcdServer.RemoveMember` (server.go:1458) | bodies, theorem, over the contracts `mayRemoveOk`, `configureRemoveOk` |
| `mayRemoveMember`, `configure` | names-only (contracts) |
| `AddMember`, `mayAddMember`, `UpdateMember`, `PromoteMember`, `promoteMember`, `isLearnerReady` | names-only: `encoding/json.Marshal`, no Perennial model |
| `apply`, `applyEntries` | bodies, theorems (`shouldStop = false`; `stopWithDelay` not reached) |
| `applyConfChange` (server.go:2025, ~78 lines) | names-only, **axiom** (`ccApplyOk`, `removed = false`) |
| `membership.RaftCluster`: `ValidateConfigurationChange`, `AddMember`, `RemoveMember`, `PromoteMember`, `UpdateRaftAttributes`; `storev2.go`'s writers | names-only |
| `RaftCluster.IsIDRemoved`, `Members`; `EtcdServer.IsIDRemoved` | bodies, theorems; `removed` proved empty (`rcLockInv`) |
| `Process`'s removed-sender check (server.go:701) | proved, never taken |
| `Stop`, `HardStop`, `stopWithDelay`, `Cleanup`, `TryTransferLeadershipOnShutdown` | names-only; no spec (D19m (A): `run` never returns) |
| `raftNode.stop`, `onStop` | theorems |

**rafthttp.** `RemovePeer`, `RemoveAllPeers`, `removePeer`, `UpdatePeer` translated with bodies, no
spec; `Stop` proved (`Stop_core`, `Stop_full` on `trFrozen`); `AddPeer` proved on `trLive` only.
The `errMemberRemoved` paths (a peer answering `403`; `checkPostResponse`, the stream's
`reportCriticalError`) are excluded by the raft protocol's "a member's handler answers no 403"
(stage 7d) and `errorc`'s `False`.

**Notes.** D21d (B) and inventory 6 (`notes/decisions.md`, around line 10270-10398): T-M as a
track after T-S, about seven new axioms (the membership writers unless translated,
`RemovePeer`/`UpdatePeer`) and `Cleanup`/`stopWithDelay` restored as true specs. D19m (B): the
stopping server's "server open" token. `notes/snapshot-s8-plan.md` W3: a true `AddPeer` after
`Start` needs an exclusive peers right that `Stop` consumes -- the same right this track needs.

## The design questions (M0, the user's)

**Q1. Which changes** (D43, to decide):
- *(A) Removal only* (recommended first): `RemoveMember` of another member and of oneself. No new
  member joins, so no join bootstrap, no snapshot to a newcomer (T-S's S-l bound untouched), no
  `json.Marshal` (`RemoveMember` and its cluster writer do not marshal), no learners.
- *(B) (A) plus adding a voter*: `AddMember` (`json.Marshal`: a model or an axiom), and a member
  that joins an existing cluster (`bootstrapExistingClusterNoWAL`: the members fetched from the
  peers over HTTP, `GetClusterFromRemotePeers`, a new protocol on the HTTP boundary), which needs
  the log from index 1 or a snapshot (T-S).
- *(C) (B) plus learners* (`PromoteMember`, `isLearnerReady`) and `UpdateMember`.

**Q2. Pre-vote in the dynamic mode.** *(A)* Extend raft's dynamic mode to pre-vote
(`reconfiguration-safety.md` 4.1: `RInv` keeps `StepR.campaign`'s guard for a pre-candidate; a
raft-side stage of unknown size, the main risk). *(B)* The example runs with `PreVote: false` (an
etcd option, `--pre-vote=false`), a premise of the closed theorem; the static examples keep
pre-vote on.

**Q3. `StepDownOnRemoval`.** *(A)* Extend the dynamic mode to `StepDownOnRemoval = false` (a removed
leader keeps leading until it learns; decisions "B5": the model already lets a leader step down at
its term, so what `sdrOk` buys must be found first). *(B)* The fork sets `StepDownOnRemoval: true`
in `bootstrap.go` (a change to the verified code; etcd-io/etcd's own choice is off).

**Q4. The stopping server's extent.** *(A)* Only the removed member's own stop: `stopWithDelay` ->
`errorc` -> `run` returns -> its deferred shutdown, with D19m (B)'s "server open" token so that
the requests in flight finish (`ErrStopped`). *(B)* Also `Stop`/`HardStop` from the application.
(A) is what removal needs.

## Stages

- **M0. Scope** (this section): Q1-Q4 with the user (**decided 2026-10-25, D43**: each (A)); W3's statement (the peers right, shared with
  S8c-S8d; **settled 2026-10-25**: `trLive`, D43 "W3 settled"); the example chosen (below). Writes D43.
- **M1. Raft clean-up (optional, warm-up)**: **done** (2026-10-25, the clean-up branch `cleanup/2026-10-24`, merged into `lean`; merged into `membership-m2` over M2c's weaker `Hvoter`). the static `ownRaftPhys` as the sealed alias of
  `ownRaftPhysC` (STATUS "Clean-up: unused declarations removed, ...": about 3-4 hours, rebuilds raft
  and the server), then `applyConfChange.specS`, `ApplyCCOk`, `SwitchOk`. Independent of the rest;
  it shrinks what M3 has to carry across modes.
- **M2. Raft: the dynamic mode as etcd's server needs it.**
  - *M2a.* `StartNode` (and `Bootstrap`) in the dynamic mode: the bootstrap's conf entries applied
    as dynamic ones from a fresh storage (today static-only).
  - *M2b.* Pre-vote in the dynamic mode, if Q2 (A).
  - *M2c.* `StepDownOnRemoval = false` in the dynamic mode, if Q3 (A).
  Each its own stage with a paper check first (`notes/reconfiguration-safety.md`), as B1 was.
  *Scoped 2026-10-25* (order: M2b, M2c, M2a):
  - **M2b done (2026-10-25)**: pre-vote in the dynamic mode proved, no premise; see `notes/decisions.md`,
    D43, "M2b". Scoping (kept): the dynamic mode excluded a pre-candidate everywhere (`RNPv`'s `s.prevote = false`,
    `PreFacts`, `GMode.Pre`, `DynHyp`; every step at a pre-candidate closed by `StepCD.of_excluded`
    with no `StepR` witness, `raft__Step/prevote_lemmas.lean:167`). The model collapses the role to
    follower (`proleRole`), so the guard goes at the node level: a pre-candidate has no pending
    snapshot and no conf entry in `(applied, commit]` (`hup`'s check, kept until the campaign: its
    log and commit do not change, 4.1), carried through `raft.Step` in the dynamic mode; the pre-vote
    win (`stepCandidate`'s `campaign`) then maps to `StepR.campaign`; `wp_applyConf_dyn`'s
    pre-candidate case from it; `RestartNode`'s `PreVote' = false` premise goes.
  - **M2c done (2026-10-25)**: `StepDownOnRemoval` either way in the dynamic mode, no premise; see
    `notes/decisions.md`, D43, "M2c". Scoping (kept): the protocol's dynamic ghost needs no step-down (4.11; `StepR`'s leader rules ask no
    voter, stage Q's `stepDown`); what needs it is the code level: `ownRaftPhysC`'s `Hvoter`
    (`role ≠ follower → id ∈ V`, `InvRaftPhys.lean:1013`), read by `stepLeader` (`Hid`),
    `MsgProp` (`Progress[id]`: Go's drop branch `raft.go:1298-1302` becomes reachable), the heartbeat
    and `MsgAppResp` responses, `becomeLeader`; `switchToConfig`/`applyConfChange`'s
    `id ∉ voters → sdr` premise and `sdrOk` go.
  - **M2a done (2026-10-25)**: `StartNode`/`Bootstrap` in either mode, the trust base unchanged; see
    `notes/decisions.md`, D43, "M2a". Scoping (kept): `StartNode`/`Bootstrap` returned the static
    mode; the allocation needed `dyn = none ∨ L = []` (`Protocol/Facts.lean:1034`): the boot log's
    conf entries are committed without a quorum, which the dynamic ghost's commit witnesses (`cqAt`)
    must admit. Done: the boot log's conf entries need no witness (the far cases close at them by
    I1, `notes/reconfiguration-safety.md` section 0); the configuration index starts at `0`, so the
    re-application of the boot entries is the ordinary dynamic `ApplyConfChange` (whose premise,
    that each decodes and applies, M3's server discharges).
- **M3. The server in the dynamic mode.** `rnEnvOk`'s `RNMode.static` replaced by the dynamic mode
  (`NodeStart`, `InvRaftNode`, `BuildGap`, `newRaftNode`: `StartNode` at `md := .dyn`, the cluster
  from `raft_dyn_alloc_boot`, M2a; the server's re-application of the boot `AddNode`s meets
  `ApplyConfChange`'s `DynCCPreOp`: its decoder, an existing member's `AddNode` a no-op or zeroed); `srvCCPolicy`/`ccApplyOk` widened to the
  kinds in scope (v1, `RemoveNode`); the static examples restated over it or kept on a static
  instance (to decide in M3: whether the static mode at the server goes, as STATUS suggests).
  **M3 done (2026-10-25, branch `membership-m3`)**: M3a-M3e as below; see `notes/decisions.md`,
  D43, "M3 carried out". The server is parametric in raft's mode; the static examples' statements
  are unchanged; the dynamic instance of the server's start is `NodeStartSpec` at `md := .dyn`
  (the server's `NewServer` passes `.static`: a dynamic `NewServer` needs a dynamic bootstrap
  contract, the example's, M8).
  *Scoped 2026-10-25* (the user's decisions, D43 "M3"): (i) the leader's `Advance` before its apply
  loop applies a conf change (`issues/etcd-leader-advance-before-applyconfchange.md`) violates raft's
  A1 in the dynamic mode (`node.Advance.spec`: `NoConfIn ds ca`), so the fork gets the drafted fix
  (the leader does the follower's second `notifyc` send); (ii) the server stays **parametric in the
  mode**: the static examples keep their statements, the dynamic one's resources are carried as raft's
  specs carry them (`⌜static⌝ ∨ nodeCfg … ∗ dlvLb …`). Sub-stages:
  - *M3a.* The fork's leader wait (`goose-lean-leaderwait`, `4d9282b0f`), re-translated;
    `raftNode.start`'s leader branch proved as the follower's (static mode: nothing changes).
  - *M3b.* `rnEnvOk` over the node's mode (its `RNMode.static` conjunct dropped where the mode is
    read: `raftPropose`'s `ApplyConfChange`, `isRaftNodeIfc`'s `Advance`); every static caller
    supplies `.static` and is unchanged.
  - *M3c.* The dynamic mode's resources through the server: the driver's `nodeCfg` and `dlvLb` from
    the raft loop to the apply thread with the `toApply` (`applyc`), back at `notifyc`'s second send.
    `notifyc` is a fresh capacity-1 channel per `Ready`, so the second send completes only once the
    apply thread has received the first, which it does after `applyEntries`: a local idiom over the
    raw channel state (`Buffered`), the apply thread depositing `nodeCfg` at its receive and the second
    send claiming it (`Spsc` keeps no capacity). A1 at `Advance` from the apply thread's applied
    conf entries.
  - *M3d.* `applyConfChange`'s `ApplyConfChange` at `DynCCPreOp`: the server's decoder
    (`ccDecodeV1`) is raft's `dec`; `ccApplyOk` (an `AddNode` of a member, the boot entries') meets
    it (an existing member's `AddNode`, applied by raft as a no-op).
  - *M3e.* `newRaftNode`/`NodeStart` at `md := .dyn` from `raft_dyn_alloc_boot` (M2a), a
    dynamic-mode instance of the server's start beside the static one.
  *Design of M3b-M3d* (2026-10-25):
  - `rnCfgAt γ L`: the driver's `nodeCfg γ.node ca cfg` with, in the dynamic mode, `NoConfIn` of
    `rnLogOf γ L` from `ca` (every conf entry handed out applied) and `cfg` the voters' simple
    configuration (no change in scope changes it yet). `rnDrv` = `nodeDriver ∗ rnCfgAt L`; `rnBusy`
    = `nodeDriverBusy ∗ rnCfgAt d` (the log before the `Ready`); `Advance` takes `rnCfgAt (d ++ ce)`.
    In the static mode `rnCfgAt` moves to any log (no pure part); in the dynamic mode, to `d ++ ce`
    when `ce` has no conf entry.
  - A batch with a conf entry, in the dynamic mode: `rnApP` carries `rnCfgAt F` and `dlvLb` of
    `F ++ ce` to the apply thread; `notifyc` is the two-send idiom (`NotifyC.lean`, over the raw
    channel state: the apply thread's receive deposits `R`, the second send, which a capacity-1
    channel admits only once the first was received, claims it) with `R = rnCfgAt (F ++ ce)`
    (`True` otherwise, the static mode's boot batch included).
  - The apply side has no `RNNames`: `apply.spec`, `applyEntries`, `applyAll` and the
    `applyConfChange` axiom take an optional driver view `dv : Option NodeNames` (`none`: the static
    mode, or a batch with no conf entry), its resource `srvCfgView γn A` (the same as `rnCfgAt`, over
    raft's names); the axiom's dynamic case calls the new contract `raftApplyCCDyn γn n` (raft's
    `node.ApplyConfChange` in the dynamic mode, `DynCCPreOp` at the server's decoder `srvDec`), the
    static clause of `raftPropose` guarded by `reDyn = none`. The replay case (`v3 = false`, an entry
    at or below the consistent index) is excluded in the dynamic mode (the consistent index is the
    batch's start, a fresh server's).
- **M4. The membership writers.** Translate `RaftCluster.RemoveMember`,
  `ValidateConfigurationChange` (its `RemoveNode` case), `mustAddToRemovedMembersInStore`, the
  backend's member delete (`schema`'s `MustDeleteMemberFromBackend`); `rcLockInv`'s `removed` map
  no longer empty, `IsIDRemoved`'s spec real (`localKept` restated: the local member may be removed).
  New Perennial gaps go to `notes/perennial-changes.md` (v2store's paths).
  **M4 done (2026-10-26, branch `membership-m4`)**: M4a-M4d as below; see `notes/decisions.md`,
  D43, "M4 carried out". (`mustAddToRemovedMembersInStore` is not in the fork's `RemoveMember`:
  the v2 store is gone.)
  *Scoped 2026-10-26* (D43 "M4"): (i) the user's decision: the fork fix of
  `issues/etcd-unary-interceptor-learner-removed.md` (`IsLocalMemberLearner` returns `false`
  for a removed local member, as etcd-io/etcd#22188; fork branch `goose-lean-learnerfix`,
  `c00a2dc06`), so a removed member's request path does not panic; (ii) `isRaftCluster` keeps its
  definition (the boot contract, `bootOk`, names it: the static examples' premises); the cluster's
  methods are proved over a general lock invariant `rcLockInvG c RM` (the removed map and the
  members map's side condition `RM`), the static `rcLockInv` its instance (`rcLocal ∗ removed
  empty`, `isMutex`'s non-expansiveness), the dynamic one with the removed map tracked
  (`dghostVar` halves, the apply thread's writer half). Sub-stages:
  - *M4a.* The fork fix pinned, `IsLocalMemberLearner` and `EtcdServer.IsLearner` translated and
    proved (the axiom `EtcdServer.IsLearner.wp_proof` goes; `localKept` leaves `IsLearner`'s and
    the interceptors' specs).
  - *M4b.* `rcLockInvG`, the methods over it (`Members`, `IsIDRemoved`, `IsLocalMemberLearner`).
  - *M4c.* `RemoveMember` translated and proved in the dynamic instance, over the member backend's
    contract (`MustDeleteMemberFromBackend`; schema's translated and proved over the backend's
    batch transaction, or a contract, decided in M4c).
  - *M4d.* `ValidateConfigurationChange` translated (its `RemoveNode` case proved, the others over
    `json.Unmarshal`'s opaque model as `ccContextOf`).
- **M5. `applyConfChange` proved** for `AddNode` of a known member and `RemoveNode`: raft's
  `ApplyConfChange` in the dynamic mode, the cluster writers (M4), `transport.RemovePeer`, and
  `removed = (id = local)`. (2026-10-25, D22 S8d: `rafthttp.Transport.RemoveAllPeers.spec` exists
  over `trLive` (`Spec/.../rafthttp/Transport__RemoveAllPeers.lean`, ids `(rs.1, [])` after; its proof
  a `sorry` on purpose, the user's decision): M5 proves it rather than restating it, beside
  `RemovePeer`; `applySnapshot` uses it.) rafthttp: `RemovePeer`/`removePeer` proved over a transport state with a
  **peers right** (W3, settled: `trLive`, not frozen by `NewServer`, held by the apply thread,
  consumed by `Stop`; the readers restated over `trState`, D43 "W3 settled"); `Process`'s removed-sender branch and the
  `403` it answers made reachable: the raft protocol's "no 403" weakened to "no 403 to a member not
  removed", `checkPostResponse`'s `errMemberRemoved` then a real error.
  *Scoped 2026-10-26* (D43 "M5"; the user's decisions): (i) `AddMember` translated and proved,
  `json.Marshal` of a `*Member` a new trust-boundary axiom over the opaque `memberEnc` (as M4d's
  `Unmarshal`); (ii) the server's dynamic policy admits `RemoveNode` of **another** member only until
  M6 (`applyConfChange`'s spec covers either, `removed = (id = local)`; `apply`'s `shouldStop` stays
  `false`); (iii) `probing.NewProber` restated: `proberOk` also promises `Remove(id)` (`removePeer`'s).
  Found while scoping: `removePeer` deletes from `LeaderStats.Followers` without the stats' lock; no
  race in the server (the map's only other writer, `Follower`, runs from `AddPeer` under the same
  transport write lock; `LeaderStats.JSON`, which reads it outside any lock, has no caller in the
  server), so the map's ownership goes in the transport's lock (`trLockP`) and `Follower` is
  translated and proved (its axiom goes). Sub-stages:
  - *M5a.* rafthttp's peer removal: `Follower` proved, `removePeer`/`RemovePeer` specified and
    proved on `trLive` (the id leaves the peers' ids), `RemoveAllPeers` proved (its `sorry` goes).
    **Done (2026-10-26, branch `membership-m5`)**: D43 "M5a carried out".
  - *M5b.* The cluster's in-memory members (`clusterMem` defined from the lock invariant, the
    user's decision) and `AddMember` translated and proved. **Done (2026-10-26)**: D43 "M5b
    carried out".
  - *M5b′* (rescoped, the user's decisions): the member backend's writers and read
    (`MustSaveMemberToBackend`, `MustDeleteMemberFromBackend`, `MustReadMembersFromBackend`)
    contract axioms over the tracked buckets (replacing the opaque `ccValidOn`), `ccRest` with
    `RemoveNode` (`members_removed`); `BackendHooks.SetConfState` translated and proved.
  - *M5c.* W3: the apply thread holds `trLive` (`NewServer` stops freezing it; the readers over
    `trState` and their tokens).
  - *M5d.* The server's cluster in the dynamic mode: `isRaftClusterG c (rcDyn γ)`, `rcRemovedOwn`
    the apply thread's; `srvCCPolicy`'s dynamic case admits a `RemoveNode` of another member.
  - *M5e.* `applyConfChange` proved (the axiom goes).
- **M6. The stopping server** (Q4 (A)): `apply`'s `shouldStop`, `stopWithDelay` translated, `errorc`
  carrying a stop request, `run`'s return and deferred shutdown (`Cleanup`, `raftNode.stop`,
  `transport.Stop` consuming the peers right), the "server open" token (D19m (B)) through every
  request path; requests on a stopped member return `ErrStopped`. The largest stage: every request
  path's spec gains the token.
- **M7. The request path of a removal.** `configure` and `mayRemoveMember` translated and proved
  (replacing the contracts `configureRemoveOk`, `mayRemoveOk`): the proposal through
  `node.ProposeConfChange` (proved), the wait registry, `ErrStopped`; the client's `MemberRemove`
  and the gRPC `ClusterServer.MemberRemove` (translate or contract, decided in M0).
- **M8. The example and its closed theorem.** A three-member cluster, a client that writes, removes
  one member (another member, then the variant removing the leader or the client's own endpoint),
  and keeps writing and reading; its safety the KV model's (as putget3's), with the removed
  member's requests failing or answered correctly before its stop. New collection
  `etc/tcb-collections/<example>.txt`; the trust check; STATUS, decisions.
- **M9. Adding a member** (Q1 (B)): a separate plan once M8 is in, on T-S's snapshot work (a
  newcomer needs the log from index 1 or a snapshot) and the join bootstrap.

## Costs and risks

- Size: comparable to rafthttp or larger (several weeks). M6 (a stopping server: every request
  path) and M2 (raft-side extensions, if chosen) carry the risk.
- M2b/M2c are proofs about raft's safety under reconfiguration with mechanisms the paper proof
  set aside; each starts with a paper check and may come back with "needs a premise" -- that is
  why Q2/Q3 have a (B).
- Shared interfaces: `Net.lean` (the network contract: `Process` refusing a removed sender) and the
  transport's start/stop rights (W3) are also the D22 owner's (S8c-S8d); changes go through both
  tracks. The auth track's `isReqAuth` reader (W2) is not touched by removal.
- Trust base: D21d's estimate was about seven axioms; with M4/M5 translated, expected fewer --
  `encoding/json` stays out with (A). `applyConfChange`'s axiom and the `configure`/`mayRemove`
  contracts go.
- The static examples must keep their theorems' statements (M3); if the static mode at the server
  goes, their `bootPremise` becomes a dynamic-mode instance whose policy admits no change.

## Open

- Whether the example's client removes members through the client library (`client/v3`'s
  `Cluster.MemberRemove`, the gRPC `ClusterServer`) or calls the server's `RemoveMember` directly
  (smaller; the API layer as a later step).
- Whether the leader's removal of itself (it leads until the entry commits, then steps down if
  `StepDownOnRemoval`) is in M8 or a later variant.
