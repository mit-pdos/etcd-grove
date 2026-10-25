# Membership changes in the server (track T-M, D21d (B)) — plan

Planned 2026-10-25. Status: **M0 in part**: Q1-Q4 decided (D43: removal only; pre-vote and
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
- **M1. Raft clean-up (optional, warm-up)**: the static `ownRaftPhys` as the sealed alias of
  `ownRaftPhysC` (STATUS "Clean-up: unused declarations removed, ...": about 3-4 hours, rebuilds raft
  and the server), then `applyConfChange.specS`, `ApplyCCOk`, `SwitchOk`. Independent of the rest;
  it shrinks what M3 has to carry across modes.
- **M2. Raft: the dynamic mode as etcd's server needs it.**
  - *M2a.* `StartNode` (and `Bootstrap`) in the dynamic mode: the bootstrap's conf entries applied
    as dynamic ones from a fresh storage (today static-only).
  - *M2b.* Pre-vote in the dynamic mode, if Q2 (A).
  - *M2c.* `StepDownOnRemoval = false` in the dynamic mode, if Q3 (A).
  Each its own stage with a paper check first (`notes/reconfiguration-safety.md`), as B1 was.
- **M3. The server in the dynamic mode.** `rnEnvOk`'s `RNMode.static` replaced by the dynamic mode
  (`NodeStart`, `InvRaftNode`, `BuildGap`, `newRaftNode`); `srvCCPolicy`/`ccApplyOk` widened to the
  kinds in scope (v1, `RemoveNode`); the static examples restated over it or kept on a static
  instance (to decide in M3: whether the static mode at the server goes, as STATUS suggests).
- **M4. The membership writers.** Translate `RaftCluster.RemoveMember`,
  `ValidateConfigurationChange` (its `RemoveNode` case), `mustAddToRemovedMembersInStore`, the
  backend's member delete (`schema`'s `MustDeleteMemberFromBackend`); `rcLockInv`'s `removed` map
  no longer empty, `IsIDRemoved`'s spec real (`localKept` restated: the local member may be removed).
  New Perennial gaps go to `notes/perennial-changes.md` (v2store's paths).
- **M5. `applyConfChange` proved** for `AddNode` of a known member and `RemoveNode`: raft's
  `ApplyConfChange` in the dynamic mode, the cluster writers (M4), `transport.RemovePeer`, and
  `removed = (id = local)`. rafthttp: `RemovePeer`/`removePeer` proved over a transport state with a
  **peers right** (W3, settled: `trLive`, not frozen by `NewServer`, held by the apply thread,
  consumed by `Stop`; the readers restated over `trState`, D43 "W3 settled"); `Process`'s removed-sender branch and the
  `403` it answers made reachable: the raft protocol's "no 403" weakened to "no 403 to a member not
  removed", `checkPostResponse`'s `errMemberRemoved` then a real error.
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
