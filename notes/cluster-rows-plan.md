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
| `SetDowngradeInfo(d, b)`, `RW` only | with `b`, `MustSaveDowngradeToBackend` (`UnsafePut(Cluster, …)`, `:809-818`) | (c) with `b`, `cluster` bucket missing: fatal (found in review round 1; `RW` lends `srvRestRW = ∃ r, rbOwn γB r`, no presence). Unreached by the workload (`rqOk`'s `downgradeInfoSet` is `False`) but a conjunct of `bootOk` |
| `Version`, `ID` | | no defect |

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
3. (c) **`srvRestOwn` holds the rest buckets present** (`restPresent r.bk`, every boot bucket since round 2, and `srvRestRW` too):
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
  `restPresent r.bk` (every boot bucket present; round 2, until then the cluster's three).
  `srvRestRWD` (trusted, the same): `∃ bk, rbOwn γB bk ∗ ⌜restPresent bk⌝` (rounds 1-2). `clusterApplyOkD`: its text over the three.
- `apply.semverAtMostServer` (new, opaque, trusted vocabulary); `apply.rqOkD` (its
  `clusterVersionSet` row with it); `monitorReqD lid` (the attribute request's member `lid`, the
  version's bound); `srvMonitorPermitMD` (the server's id field, a voter, the permission for
  `monitorReqD lid`). These change what `publishV3`'s and `monitorClusterVersions`' axioms
  claim, their texts unchanged.
- Untrusted: `ClusterVersionSet.specD` (premise `semverValid v ∧ semverAtMostServer v`),
  `ClusterMemberAttrSet.specD` (premise the member in `rs.mem`), `apply.clusterFactsD E m cr r rs`
  (the applier contract's cluster facts with the rest state: the version's bound, the member; round
  1: `dispatch` reaches the methods through the contract, not the specs), `apply.restReqOk rq rs`
  (the dispatch's premise), `attrIdOk` (with `irrNoZeroEnd` for an attribute request, so that the
  wire decodes the request itself: a cluster kind wins `dispatchKind` over a range with a zero end,
  round 1)/`attrEntryOk`/`attrLogOk`, `kvWorkD` (with `attrLogOk`),
  `reqPropOkMD` (with `attrIdOk`), `srvMemOkD` (with `srvMemCover`), `rqShapeD` (rqShape read under
  `rqOkD`).

The glue proved against them (no `sorry`): `ClusterVersionSet.wp_proofD` (the program's `onSet`
is the row's value; the bound passed), `ClusterMemberAttrSet.wp_proofD`; `rqOk_of_rqOkD`,
`rqOkD_ver`, `restReqOk_attr` (dispatch's two call sites, into `clusterFactsD`), `rqOkD_of_rqOk`
(the other producers of `rqShape`), `apply.clusterRow_backendD` (`newApplierV3Backend`'s cluster row
over `clusterFactsD` from the restated specs); `restPresent_congr` (the revocation lens);
`attrIdOk_wire` (beside `reqPropOk_wire`); `srvApRes_lid` (`Start`'s permit); `restPresent_restBoot`,
`_restModel`, `_restSetVersion`, `_restUpdateAttrs`, `_ccRest`; `memBoot_cover`,
`srvMemOkD_boot`, `srvMemCover_normal`, `ccRest_memKeys_mono`, `srvMemOkD_append`;
`restReqOk_of_attr` (EtcdServer.apply's premise for `apply.Apply`); `attrEntryOk_of`,
`kvWorkD_snoc` (the KV acceptance); `rqShapeD_of_monitorReqD`, `attrIdOk_of_monitorReqD`,
`srvMonitorPermitMD_of` (the permit from the request view, the id field and `srvDynLog`, which
`Start` extracts from `isServerBuilt`'s `srvApRes s γr []` with `srvApRes_lid`),
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
3. `srvRestOwn` (§16's, `InvRest.lean:414`): `restPresent r.bk`; `srvRestRW`
   (`InvRest.lean:420`): `restPresent` of its buckets. Through them `clusterApplyOk` and `bootOk`
   (texts unchanged), and the alarm and auth stores' contracts, whose `rwLens` lend `srvRestRW`
   (they now claim their writers keep the cluster's buckets: they write only their own).
4. `apply.semverAtMostServer` (new opaque, `apply/InvRequest.lean` beside `semverValid`);
   `apply.rqOk`'s `clusterVersionSet` row (`apply/Chain.lean:267`).
5. `monitorReq` (`InvMonitors.lean:54`) gains `lid`; `srvMonitorPermit` (`InvMonitors.lean:81`) and
   `srvMonitorPermitM` (`MonitorsOn.lean:62`): the id field, a voter. The axioms
   `EtcdServer.publishV3` and `EtcdServer.monitorClusterVersions` (texts unchanged) now claim
   their proposals name the server's id and a version not above the server's.

Untrusted, the changes each needs:

- `apply/applierV3backend__ClusterVersionSet` (spec, proof: as `…D`); `…ClusterMemberAttrSet`
  (as `…D`); `apply/Chain.lean` (`clusterFacts` as `clusterFactsD`, the applier contract's cluster row
  passes `rs`); `apply/newApplierV3Backend` (its cluster row: `clusterRow_backendD`); the wrappers
  `newAuthApplierV3`, `newQuotaApplierV3`, the capped and corrupt appliers (pass-through: the new
  argument); `apply/uberApplier__dispatch` (spec gains `⌜restReqOk rq rs⌝`; proof: the two call
  sites build `clusterFactsD` from `rqOkD_ver`/`restReqOk_attr`); `uberApplier__Apply`, `apply/Apply` (spec gains the premise,
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
  `KVLemmas.reqPropOk_wire`'s users (`attrIdOk_wire`), `InvProposer`/`ReqOn`/`EtcdServer__Compact`/
  `KVAuthModel`/`ProposeOn` (`rqShape` under `rqOkD`: `rqOkD_of_rqOk`),
  `MonitorsOn`/`InvMonitors` (`srvMonitorPermitMD_of`), `EtcdServer__Start` (`:103,133,248,278`:
  `srvApRes_lid` from `isServerBuilt`, then the permit).
- `InvApRes` (`srvMemOk` as `srvMemOkD`; `srvMemOk_boot`, `srvApRes_normal`, `srvMemOk_append`,
  `srvApRes_cc` with the cover), `ApplyAllSnap`, `NewServer` (`srvMemOkD_boot`).
- `srvRestRW`'s lenses (`SnapApplyOptsLemmas.lean:41-82`, `srvRestRWH_lens_*`: the pure conjunct
  carried; no producer of `srvRestRW` exists, the write right is never owned in the workload).
- `srvRestOwn`'s producers and destructurings (`restPresent`; the revocation lens
  `srvRestOwnH_lens_revoke` with `restPresent_congr`): `NewServer` (`restBoot`),
  `SnapApplyRest.snap_srvRest` (`restPresent_restModel`), `EtcdServer__applyConfChange`
  (`restPresent_ccRest`), `SnapRO` (the lenses), `SnapRecvFacts`, `SnapApplyWalk`,
  `SnapApplyDefs`, `SnapApplyOptsLemmas` (the positional destructurings §16 already lists).
- `memberAt`'s users: `Member__Clone`, `RaftCluster__AddMember`, `__Members`, `__RemoveMember`,
  `__IsLocalMemberLearner` (proofs reopen the member: the client URLs persistent),
  `EtcdServer__applyConfChange` (the unmarshalled member's client URLs made read-only before
  `AddMember`, `memberAt_persistD`).

## Review

**Round 1** (a fresh `spec-reviewer`, given the targets, the Go code and the callers). First tier:

- F1: `SetDowngradeInfo`'s row has defect (c) (fatal on a missing `cluster` bucket), and `RW`'s
  `srvRestRW` holds no presence. Repaired: `srvRestRWD` (presence), `clusterApplyOkD` over it; Go:
  `TestClrTodayMissingBucketFatal`'s `downgrade` case.
- F2: `dispatch` reaches the cluster methods through the applier contract's row (`Chain.lean:1368`,
  `clusterFacts`), not the two specs; `newApplierV3Backend` could not feed the restated specs.
  Repaired: `apply.clusterFactsD` (with `rs`), `apply.clusterRow_backendD` (proved); Impact gains
  `Chain`, `newApplierV3Backend`, the wrappers.

Second and third tier, repaired: `Start` (not `NewServer`) builds the monitors' permit
(`srvApRes_lid`, the docstring); the revocation lens's congruence (`clusterPresent_congr`); the
converse `rqOkD_of_rqOk`; `attrIdOk` across the wire (found while repairing: the wire law needs
`irrNoZeroEnd`, now in `attrIdOk`; `attrIdOk_wire`); the misnamed and duplicate presence lemmas
removed; docstrings (`semverAtMostServer`'s argument, `rcLockInv` in `memberAtD`'s, the value size
not claimed). Not repaired, questions: `isPkgInit api` in `SetVersion`'s row (`UpdateCapability`
reads `api`'s globals); `clusterImageOk_restModel`'s axiom could take the version bound from the log
instead of the deployment. Outside the targets: `RaftCluster__Recover.lean:43`'s docstring says
`MustDetectDowngrade` rejects a version "below its minor by more than one"; Go has no lower bound.

**Round 2** (fresh). First tier:

- F1: `attrEntryOk` had no empty-data guard, and the committed log holds raft's empty no-op
  entries (`BuildGap.lean:150-151`), for which `irrDecode []` (opaque) says nothing: `attrLogOk` was
  unprovable for a real batch. Repaired: `attrEntryOk S m := m.typ = 0 → m.data ≠ [] → …` (as
  `KVAuthModel.lean:611`), `attrEntryOk_empty`; `restReqOk_of_attr` takes `m.data ≠ []`, which
  `applyEntryNormal` has after its empty-data return (`server.go:1989-1998`).
- F2: the alarm and auth stores' writers lend the same `srvRestRW` and are fatal on their own
  missing buckets (Go: `TestClrTodayMissingBucketFatal`'s `alarm` case). Repaired: the presence
  predicate is every boot bucket (`restPresent`, `restBootBk`'s; was `clusterPresent`, the cluster's
  three), in both `srvRestOwnD` and `srvRestRWD`; `restPresent_congr` takes the agreement off
  `lease` with `lease` present.

Second tier, repaired: `SetVersion`'s row takes `isPkgInit membership ∗ isPkgInit api` (as
`Recover`'s axiom; the glue derives both with `iPkgInit`); `semverAtMostServer`'s docstring (the
`MinClusterVersion` case; the one-binary deployment the applying member's bound rests on); the
trusted `monitorReq` is the draft's `monitorReqD` exactly; the order of application (§16 first).
Not traced, a question: the lessor's `lease` bucket through `lessorApplyOk`'s `Rb`.

## Questions for the user

See `clr-trusted.md` (the scratch file of the trusted texts) and the stage report.
