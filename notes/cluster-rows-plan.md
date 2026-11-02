# The cluster contract's rows (spec-first: Scope, Draft, Impact, Review)

Branch `cluster-rows` (2026-11-02), off `backend-auth-split`'s committed head `ba51647f9c`. The
stage the user decided on 2026-11-02 (Q9, `notes/backend-auth-split-plan.md`, "Next stage"): the
rows of `bootOk`'s cluster contract (`clusterApplyOk`, `SnapRO.lean:193`; the rows are
`apply.isCluster`'s, `apply/Contracts.lean:525-549`) are false of Go at some rest states. A false
conjunct of `bootPremise` makes the closed results vacuous there, not unsound. Draft modules
(imported by nothing, no `axiom`, no `sorry`):
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/ClusterRowsDraft.lean` (the rows, their two
callers' specs and proofs, the request premises) and
`Proof/go_etcd_io/etcd/server/v3/etcdserver/ClusterRowsDraft.lean` (the rest resource, the
members' vocabulary, the workload facts, the glue). Status: Draft and Review done, stopped before
Freeze; the trusted texts for the user's approval are in the session's scratch `clr-trusted.md`.

Built on backend-auth-split's approved trusted restatements (its `bks-trusted.md`, revision 4.3,
§16: `srvRestOwn` over `rbOwnIn`/`rbPart` with `memIdOk`), which this base has not applied yet:
`srvRestOwnD` is §16's text with this stage's conjunct.

## Scope

### The rows and what Go does (fork pin `ab3c28d9a`)

`clusterApplyOk c` gives, at every real backend `d` and every rest resource `RO` lending
`srvRestOwn d.γB c r ∗ clusterBeOn c d.be`, the apply package's `isCluster c …`, whose rows the
trusted contract asserts of the real `*membership.RaftCluster`:

| row | Go (`server/etcdserver/api/membership/cluster.go`) | false where |
|---|---|---|
| `SetVersion(v, onSet, b)`, any `onSet`, any version `s`, any `r` | `c.version = ver`; `MustDetectDowngrade(lg, MustParse(version.Version), ver)` (`:609-611`); with `b` `MustSaveClusterVersionToBackend` (`UnsafePut(Cluster, …)`); `onSet(lg, ver)` (`:623`) | (b) `s` above `3.8.0` (the server's major.minor, patch 0): `lg.Panic` (`version/downgrade.go:48-53`); also `3.8.1`; (e) a panicking `onSet`; (c) with `b`, `cluster` bucket missing: `lg.Fatal` (`backend/batch_tx.go:169-173`) |
| `UpdateAttributes(id, attr, b)`, any `id`, any `r` | member: `m.Attributes = attr` (`:472`), with `b` `MustSaveMemberToBackend(m)`; removed: a warning; else `lg.Panic` (`:479-486`) | (a) `id` neither member nor removed (with or without `b`); (c) with `b`, `members` bucket missing: fatal; (d) the post's members own halves of the client URLs' elements (`memberAt`'s `cu ↦*{own ½}`) while Go stores the request's slice itself, which the caller holds read-only (`↦*□`, `memberAttrSetIs`): an ownership claim the heap does not have (not refutable by a panic; shown by aliasing) |
| `Version`, `ID`, `SetDowngradeInfo` | | not this stage's (no defect found) |

(d) is confirmed (it was "unconfirmed" in the decision): the pre's `attr.ClientURLs' ↦*□ cus`
cannot give the owned `½` the post's `clusterMem` holds (`memberAt`, `api/membership/Defs.lean:99`).
(e) is new (found in Scope): the row quantifies over `onSet : val`.

### The callers of the rows, and who discharges what

- `apply.applierV3backend.ClusterVersionSet` (proved): calls `SetVersion(MustParse(r.Ver),
  api.UpdateCapability, v3)`. Today's premise `semverValid v` (from `dispatch`'s `rqOk`).
- `apply.applierV3backend.ClusterMemberAttrSet` (proved): calls `UpdateAttributes(r.Member_ID,
  {Name, ClientUrls}, v3)`; holds the request read-only (`memberAttrSetIs`).
- `uberApplier.dispatch` (proved) calls both, with `E.RO rs` and `⌜rqOk log rq⌝`; above it
  `uberApplier.Apply`, `apply.Apply`, `EtcdServer.applyEntryNormal`/`EtcdServer.apply` (where `rs`
  is `restModel c0 boot (pre ++ A)`, `srvRest`, and the entry's request is the committed log's),
  `applyAll`, `applyEntries`, `run` (the log facts from the KV invariant: `logShape`, InvBuild's
  batch facts).
- `RO` is built (`srvRestOwn`'s producers) by `NewServer` (`restBoot`), the snapshot path
  (`snap_srvRest`: `restModel … A'`), `applyConfChange`'s rebuilds after `ccRest`, the lessor's
  revocation lens.
- The requests come from the server's own goroutines (names-only axioms): `publishV3`
  (`Member_ID: uint64(s.MemberID())`, `server.go:1828-1853`) and `monitorClusterVersions`
  (`version.Monitor.UpdateClusterVersionIfNeeded`: the minimum of the members' versions, the local
  member's `version.Version` among them, cut to `Major.Minor.0`; `MinClusterVersion` `3.0.0`
  before any; the downgrade branch unreachable: no `DowngradeInfoSet` is admitted, `rqOk`), with
  the permission `srvMonitorPermitM`, for the requests `monitorReq` admits.
- The server's membership is static after boot (`ccApplyOk`: only `AddNode`s of the boot
  configuration), so no member is ever removed: the removed case of `UpdateAttributes` is not
  reached and need not be claimed.

### Decisions of Scope (each a question below)

1. (a) **A row premise, the id a member of `r.mem`** (not "or removed": the server removes none;
   claiming the warning case would need the contract to know Go's `c.removed`, which no resource
   models). Discharged at `EtcdServer.apply` from two facts: the committed log's attribute
   requests name voters (`attrLogOk cfg`, a new conjunct of the KV invariant's workload facts,
   carried by the proposal permission: the request path's name no attribute request, the
   monitors' the server's own id, a voter); and the voters are members of the rest state at every
   applied log (`srvMemOk` gains its converse, `srvMemCover`).
2. (b) **A row premise on the version** (`semverAtMostServer s`, opaque as `semverValid`), a
   request premise (`rqOk`'s `ClusterVersionSet` row), from the monitor's requests (`monitorReq`
   narrowed, which `monitorClusterVersions`' axiom claims).
3. (c) **`srvRestOwn` holds the cluster's buckets present** (`clusterPresent r.bk`, as decided):
   every model rest state has them (`restModel_present`), the rows and `applyConfChange` keep them.
4. (d) **The members' client URLs read-only** (`memberAt` with `cu ↦*□`): true of Go (no writer of
   a member's `ClientURLs` elements: `Clone` copies, the writers replace the slice); the rows'
   texts then need no change for it. Its alternatives (the row taking an owned slice; the request
   decoded owned) need ownership no caller has.
5. (e) **`onSet` fixed to `api.UpdateCapability`** (the one value passed), not a callback
   contract (which would need a new trust-boundary spec of `UpdateCapability`).

## Draft

The restated statements (`…D` replaces the unsuffixed in place at the switch):

- `apply.isClusterD` (trusted): `SetVersion`'s `onSet := @! api.UpdateCapability`, premise
  `⌜semverAtMostServer s⌝`; `UpdateAttributes`' premise `⌜(r.mem.lookup id).isSome⌝`; the other
  rows unchanged.
- `membership.memberAtD` (trusted vocabulary, in place: `memAt`, `clusterMem`, `clusterMemIn`,
  `isRaftCluster(G)` carry it): `cu ↦*□ mm.clientURLs`. Laws `memberAtD_split`,
  `memberAtD_agree`, `memberAt_persistD` (today's to the restated, an update).
- `srvRestOwnD` (trusted, through `clusterApplyOk`): §16's text over `clusterMemD`, with
  `membership.clusterPresent r.bk`. `clusterApplyOkD`: its text over the two.
- `apply.semverAtMostServer` (new, opaque, trusted vocabulary); `apply.rqOkD` (its
  `clusterVersionSet` row with it); `monitorReqD lid` (the attribute request's member `lid`, the
  version's bound); `srvMonitorPermitMD` (the server's id field, a voter, the permission for
  `monitorReqD lid`). These change what `publishV3`'s and `monitorClusterVersions`' axioms
  claim, their texts unchanged.
- Untrusted: `ClusterVersionSet.specD` (premise `semverValid v ∧ semverAtMostServer v`),
  `ClusterMemberAttrSet.specD` (premise the member in `rs.mem`), `apply.restReqOk rq rs` (the
  dispatch's premise), `attrIdOk`/`attrEntryOk`/`attrLogOk`, `kvWorkD` (with `attrLogOk`),
  `reqPropOkMD` (with `attrIdOk`), `srvMemOkD` (with `srvMemCover`), `rqShapeD` (rqShape read under
  `rqOkD`).

The glue proved against them (no `sorry`): `ClusterVersionSet.wp_proofD` (the program's `onSet`
is the row's value; the bound passed), `ClusterMemberAttrSet.wp_proofD`; `rqOk_of_rqOkD`,
`rqOkD_ver`, `restReqOk_attr` (dispatch's two call sites); `clusterPresent_restBoot`,
`_restModel`, `_restSetVersion`, `_restUpdateAttrs`, `_ccRest`; `memBoot_cover`,
`srvMemOkD_boot`, `srvMemCover_normal`, `ccRest_memKeys_mono`, `srvMemOkD_append`;
`restReqOk_of_attr` (EtcdServer.apply's premise for `apply.Apply`); `attrEntryOk_of`,
`kvWorkD_snoc` (the KV acceptance); `rqShapeD_of_monitorReqD`, `attrIdOk_of_monitorReqD`,
`srvMonitorPermitMD_of` (the permit from the request view, the id field and `srvDynLog`),
`reqPropOkMD_of_kind` (the request path's other permissions).

Not proved in the Draft (mechanical at the switch, listed in Impact): `dispatch`'s proof with the
new premise (its two call sites are `rqOkD_ver` and `restReqOk_attr`), the chain's specs above it
taking `restReqOk`, the KV acceptance's three cases (`kv_prop_auW`, the mode-on's) using
`kvWorkD_snoc` with `attrEntryOk_of`, `EtcdServer.apply`'s proof using `restReqOk_of_attr`, and
the `memberAt` users re-proved over `memberAtD` (`AddMember`, `Clone`, `applyConfChange`'s
`memberAt_persistD`).

## Impact (nothing applied)

Trusted texts (for the user's approval, `clr-trusted.md`):

1. `apply.isCluster` (`apply/Contracts.lean:509-544`): the two rows; docstring.
2. `membership.memberAt` (`api/membership/Defs.lean:99`): `cu ↦*□`; its laws
   (`memberAt_split`, `memberAt_agree`; `memberIs_iff_memberAt` keeps only `→`, unused). The axioms
   whose meaning changes through it, each weaker in a post or reading only in a pre:
   `RaftCluster.Recover`, `clusterImageOk_restModel`, `MustSaveMemberToBackend`,
   `setIsLearnerMetric`, `SetBackend`, `String`, `updateMembershipMetric`,
   `SetVersionChangedNotifier` (through `isRaftCluster`'s lock invariant), the v3rpc interceptors'
   `IsMemberExist`/`IsLearner`; `bootOk`'s `Hmem` (text unchanged).
3. `srvRestOwn` (§16's, `InvRest.lean:414`): `clusterPresent r.bk`. Through it `clusterApplyOk`
   and `bootOk` (texts unchanged).
4. `apply.semverAtMostServer` (new opaque, `apply/InvRequest.lean` beside `semverValid`);
   `apply.rqOk`'s `clusterVersionSet` row (`apply/Chain.lean:267`).
5. `monitorReq` (`InvMonitors.lean:54`) gains `lid`; `srvMonitorPermit` (`InvMonitors.lean:81`) and
   `srvMonitorPermitM` (`MonitorsOn.lean:62`): the id field, a voter. The axioms
   `EtcdServer.publishV3` and `EtcdServer.monitorClusterVersions` (texts unchanged) now claim
   their proposals name the server's id and a version not above the server's.

Untrusted, the changes each needs:

- `apply/applierV3backend__ClusterVersionSet` (spec, proof: as `…D`); `…ClusterMemberAttrSet`
  (as `…D`); `apply/uberApplier__dispatch` (spec gains `⌜restReqOk rq rs⌝`; proof: the two call
  sites, `rqOkD_ver`/`restReqOk_attr`); `uberApplier__Apply`, `apply/Apply` (spec gains the premise,
  passed); `apply/ApplyKVL`, `DispatchKVL`, `ApplyAdmin`, `ApplyRec`, `InvUber` (users of the rest
  effects: unchanged unless they call `dispatch`'s spec, then pass the premise).
- `EtcdServer__applyEntryNormal`, `EtcdServer__apply` (spec gains `⌜attrLogOk ρ.raft.raft.cfg ms⌝`;
  proof: `restReqOk_of_attr` from `srvApRes`'s `srvMemOkD`), `EtcdServer__applyAll`,
  `EtcdServer__applyEntries`, `ModeSpecs` (the premise passed), `EtcdServer__run`, `InvRun`,
  `InvBuild` (the batch facts give `attrLogOk` with `logShape`), `RunOn`.
- `InvRequest` (`kvWork`: `attrLogOk`), `KVAuthModel` (`kvWorkOn`), `KVLemmas` (`kvWork_snoc` as
  `kvWorkD_snoc`, `kv_prop_auW`'s three cases with `attrEntryOk_of`), `ProposeOn` (the mode-on
  acceptance), `ReqOn` (`reqPropOkM` with `attrIdOk`; its producers `reqPropOkMD_of_kind`),
  `EtcdServer__Put`/`Txn`/`DeleteRange`/`Compact` and the admin requests' proofs (one line each),
  `MonitorsOn`/`InvMonitors` (`srvMonitorPermitMD_of`), `NewServer`/`StartOn`/`InvStart` (build the
  permit with `srvApRes`'s id and `srvDynLog`).
- `InvApRes` (`srvMemOk` as `srvMemOkD`; `srvMemOk_boot`, `srvApRes_normal`, `srvMemOk_append`,
  `srvApRes_cc` with the cover), `ApplyAllSnap`, `NewServer` (`srvMemOkD_boot`).
- `srvRestOwn`'s producers and destructurings (`clusterPresent`): `NewServer` (`restBoot`),
  `SnapApplyRest.snap_srvRest` (`clusterPresent_restModel`), `EtcdServer__applyConfChange`
  (`clusterPresent_ccRest`), `SnapRO` (the lenses), `SnapRecvFacts`, `SnapApplyWalk`,
  `SnapApplyDefs`, `SnapApplyOptsLemmas` (the positional destructurings §16 already lists).
- `memberAt`'s users: `Member__Clone`, `RaftCluster__AddMember`, `__Members`, `__RemoveMember`,
  `__IsLocalMemberLearner` (proofs reopen the member: the client URLs persistent),
  `EtcdServer__applyConfChange` (the unmarshalled member's client URLs made read-only before
  `AddMember`, `memberAt_persistD`).

## Review

See the end of this note (rounds, findings, repairs).

## Questions for the user

See `clr-trusted.md` (the scratch file of the trusted texts) and the stage report.
