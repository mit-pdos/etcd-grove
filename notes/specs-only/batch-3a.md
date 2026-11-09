# Batch 3a: etcd's apply layer (`server/etcdserver/apply`)

Author's report, 2026-11-09. Namespace `Apply`. Every file builds (`etc/specs-build.sh --dir
Spec/go_etcd_io/etcd/server/v3/etcdserver/apply`: 74 modules OK).

## Files

- `Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/Api.lean`: the model of one apply and the
  resources (header: meaning, realization, laws, snippets).
- `Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/ApiResult.lean`: the result predicate over 2c's
  `applyResult`, `checksOut`, and the uber-applier's interface bundle `isUber_apply` (kept apart so
  the model does not import the request path's vocabulary).
- 72 spec files, one per function of the old specs (all 72 kept):
  - the client-facing core, written with full care: `Apply`, `NewUberApplier`,
    `uberApplier__Apply`, `CheckTxnAuth`;
  - the uber-applier's helpers: `uberApplier__{dispatch,Alarm,restoreAlarms}`;
  - the chain's `Apply`s: `authApplierV3__Apply`, `applierV3backend__Apply`;
  - the layer methods, over one shared relation (`layersStep`):
    - `applierV3backend__*` (26 request methods);
    - `applierV3backend__{newHeader,ClusterVersionSet,ClusterMemberAttrSet,DowngradeInfoSet}`;
    - `authApplierV3__{Put,Range,DeleteRange,Txn,LeaseRevoke,UserGet,RoleGet}`;
    - `quotaApplierV3__{Put,Txn,LeaseGrant}`;
    - `applierV3Capped__{Put,Txn,LeaseGrant}`;
    - `applierV3Corrupt__{Put,Range,DeleteRange,Txn,Compaction,LeaseGrant,LeaseRevoke}`;
  - the constructors: `newApplierV3`, `newApplierV3Backend`, `newQuotaApplierV3`,
    `newAuthApplierV3`, `newApplierV3Capped`, `newApplierV3Corrupt`;
  - the checks: `checkPutAuth`, `checkTxnPermission`, `checkTxnReqsPermission`, `checkLeasePuts`,
    `checkLeasePutsKeys`, `needAdminPermission`, `noSideEffect`.
  The layer methods' files were generated from one template (`/tmp/gen3a/gen*.py`, not
  committed); each has the block comment (Users, Proof sketch, Changes, Margin).
- Snippets: `examples/specreq/apply/` (`apply.go`, `alarm.go`, `auth.go`; `go vet` clean).
- New non-issue: `nonissues/etcd-apply-quota-nospace-after-write.md` (index regenerated).

## Exported vocabulary

**The model (pure, transparent unless said):**
- `MemberCfg` (`minLeaseTTL`), `MemberCfg.ok`.
- `Hdr`, `AlarmAct`, `IrrOp`, `Irr`: the decoded request. `IrrOp` covers:
  - W0's `Req` for the kinds raft carries (`reqIsIrr`);
  - the hashed user changes;
  - `authenticate`, the alarm actions, the checkpoint;
  - the membership requests.
- Accessors: `Irr.reqId`, `hasId`, `user`, `revW`, `authRev`, `who`, `hdrOk`.
- Classifiers: `IrrOp.needAdmin`, `noSideEffect`, `isMembership`, `isTxn`, `corruptRefused`,
  `cappedRefused`, `quotaWrite`.
- The gates:
  - `Layer`, `baseLayers`, `chainLayers σ`: the chain the alarms select;
  - `adminErr`, `preErr`, `opErr`, `leaseErr`, `checkErr`, `firstErr`: `IsAdminPermitted` and
    `isOpPermitted`, including the stale-revision refusal;
  - `Check`, `putChecks`, `RequestOp.checks`, `authErr`, `layersErr`.
- `opStep` (**opaque**, a function): the backend's operation. Its meaning is fixed by its laws.
- `alarmStep`, `layersStep`, `irrStep mc σ ir v3 σ' res` (**the apply's step**), `noAns`, `publish`.
- `irrDecodes` (opaque, provisional for 3h).
- `applyStep mc σ e σ' res`: 2d's name and signature.
- Admission: `authRecordFits` (opaque, provisional for 3d), `clusterVerOk` (opaque, provisional for
  2e), `txnAdmitted`, `reqAdmitted`, `IrrOp.ok`.
- TTL variance: `eraseTTL`, `ttlEq`, `respTtlEq`.
- What a result carries: `OpResp.skip`, `skipRanges`, `resMatch`.
- In `ApiResult.lean`: `opBody op b`, the request as 2c's `IrrBody` (relational, because a token's
  checked revision is not in the entry), and `resultAt γ ar ir sk res`, the `*apply.Result`.

**Resources:**
- `isUber ua mc γ γc R` (persistent): the uber-applier.
- `smAt ua σ` (exclusive): the member's state machine at `σ`.
- `memberUpd γc op Q`: for a publication, the caller's atomic update of 2e's `clusterSt`.
- The options' slots: `optsOk`, `optsSt`.
- Provisional, to be replaced by the owning batch's names:

  | name | owner |
  |---|---|
  | `kvOk`, `kvSt` | 3e |
  | `lessorOk`, `lessorSt`, `lessorRead` | 3c |
  | `authOk`, `authSt`, `authRead` | 3d |
  | `permReads` | 3d and 3c |
  | `statusOk`, `snapSrvOk`, `ciOk` | 2d |
  | `irrMsgAt`, `reqMsgAt` | 3h |
- Internal, for the package's own specs: `beAt`, `stAt`, `applierAt`, `aiAt`, `uberAt`,
  `uberChain`, `beOpts`, `wrapperAt`, `replyAt`, `checksOut`.

**Laws:**
- Resource laws: `persistent`, `smAt_timeless`, `smAt_excl`, `aiAt_excl`, `smAt_unfold` (internal).
- Laws of the model:
  - `irrDecodes_fun`;
  - `opStep_fun`, `opStep_total`;
  - `opStep_step`: a client request's backend operation is W0's `Step`;
  - `opStep_authenticate`, `opStep_userAdd`, `opStep_userChangePassword`, `opStep_ttl`.
- Consequences, for 2c and 2d:
  - `irrStep_fun`, `applyStep_fun`, `applyStep_total`;
  - `irrStep_step`: a client request's apply is `Step ir.who rq` in every mode;
  - `irrStep_env`: an activation or a publication is an `EnvStep`, or nothing;
  - `irrStep_quiet`, `irrStep_noV3`;
  - `irrStep_oldRev`: a stale revision changes nothing;
  - `irrStep_ttl`.
- `replyAt_result`; `isUber_apply`, the method bundle in the approved parametric shape.

## How 2d's provisional names map

| 2d's provisional name | 3a's name |
|---|---|
| `EtcdServer.MemberCfg` (opaque type) | `Apply.MemberCfg` (structure) |
| `EtcdServer.applyStep` (opaque) | `Apply.applyStep`, same signature, now transparent |
| `EtcdServer.applyStep_fun.spec` | `Apply.applyStep_fun.spec`, same statement |
| 2c's `applyResult γ x ir res` | `Apply.resultAt γ ar ir sk res`, which wraps it |
| the uber-applier's contract | `Apply.isUber` + `isUber_apply.spec` + `smAt` |

## Main changes from the old specs

Old specs: `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/`, 72 files.

- **One triple per function, every mode**: auth on and off, the alarms (the capped and corrupt
  chains), leases, compaction, the replay, every request kind. The old two-mode chain predicates are
  gone: `AEnv`, `chainRes`, `kvOwnPre`, `certPreV`, `ltHalf`, `everOwn`, `grantFresh`, `revokeOwn`,
  `cmpOwn`, `restReqOk`. So are the 25 premises of `uberApplier.Apply`. The state is W0's model
  state, and the answer is the step's.
- **`backendUnderQuota` is gone.** The quota's `ErrNoSpace` is a margin of the result (`resMatch`).
- **Determinism is a law.** `opStep` is opaque because W0 leaves sorts, and therefore answers,
  relational.
- **`CheckTxnAuth`** is stated over the cluster's reached auth states (`authTables`), each check at
  its own state. The checks are not atomic, and a token may come from another member.
- **The permission checks**:
  - The stale auth revision (`ErrAuthOldRevision`) is modelled exactly (`opErr`).
  - The administrator check (`adminErr`) has no revision check, as in Go.
  - The helper checks have one spec each, parametric in the states their reads see (`permReads`).
    It serves both the apply thread (exact) and the request path.
- **Membership:**
  - publications change the model's members (`EnvStep.publish`), through 2e's
    `UpdateAttributes`;
  - the version and the downgrade info are outside the model; the version's panic-freedom is
    `clusterVerOk`.

## Functions left out

None. The old spec files are all restated, and no Go function of the package lacks a spec. Not
specified: the metrics (`metrics.go`, names only) and goose's promoted-method wrappers, which are not
Go functions.

## Decisions for the user

1. **Members configured differently** (the lessor's minimum TTL follows the election timeout).
   - What happens: each member raises a grant's TTL to its own minimum, so the members' lease tables
     differ in the TTLs.
   - Chosen: the apply takes the member's configuration, and the cluster's history records the
     proposer's TTL. Every other member's state machine equals the history up to the TTLs
     (`ttlEq`, `irrStep_ttl`). This needs no premise.
   - Alternative: a premise on `NewServer` that every member has the same minimum. 2d's histories
     would then be exact per member, but it restricts deployments that etcd allows.
2. **`ErrNoSpace` after an applied write**
   (`nonissues/etcd-apply-quota-nospace-after-write.md`).
   - What happens: when a member's backend is over its quota, a put, a write transaction or a grant
     is applied, and the client is still told "database space exceeded".
   - Chosen: the spec says so (`resMatch`), and W0 is asked to make `ErrNoSpace` an error that
     settles nothing (`req/go_etcd_io_etcd_api_v3.md`, item 1).
   - Cost: a client that sees `ErrNoSpace` learns nothing, even when the refusal really happened
     before proposing.
   - Alternative: the old workload premise "the backend stays under its quota"
     (`backendUnderQuota`).
3. **Passwords in the model.** The apply only ever sees bcrypt's hash, so W0 is asked to model the
   stored credential with a trusted `pwMatch` (W0's item 2). Otherwise the model state is not a
   function of the log.
4. **The cluster version.** A `ClusterVersionSet` panics on an unparsable version or one above the
   member's binary (`clusterVerOk`). This needs either a cluster invariant (the leader proposes the
   minimum of the members' versions) or a deployment premise (no member runs a binary older than the
   cluster version). It is 2e's to settle.

## Open questions, sent to other batches

- **2c**: `Wait.list.IsRegistered`'s `false` should give a persistent "not registered" fact. Without
  it, `Apply.spec`'s skipped transaction and its `nil` return are a margin, and 2d's `Trigger` of a
  skipped result is unjustified. 2c should also accept `resMatch` (an alarm list in any order;
  `ErrNoSpace` as outcome 3).
- **2e/2d**: the alarm store's view is read concurrently by the request path (`Alarms()`), so it
  needs a writer/reader split. `BackendQuota.Cost` must be exact for the capped applier.
  `SetVersion` and `SetDowngradeInfo` need specs.
- **3b/3c/3d/3e**: replace the provisional slots and establish `opStep`'s laws (requests below).

## Requirement sections written (`## from 3a`)

| file | what it asks |
|---|---|
| `req/go_etcd_io_etcd_api_v3.md` (W0) | `noSpace` indefinite; the stored credential; no user with the empty name; grant TTLs |
| `req/go_etcd_io_etcd_server_v3_etcdserver.md` (2c, 2d) | the name mapping, `isUber`/`R`/`memberUpd`/`smAt`'s TTL variance, `resultAt`/`resMatch`, `CheckTxnAuth`, `IsRegistered`'s fact, `irrDecodes` |
| `req/go_etcd_io_etcd_server_v3_etcdserver_txn.md` (3b) | each operation a deterministic `Step`; the skipped ranges; no panic |
| `req/go_etcd_io_etcd_server_v3_lease.md` (3c) | `Grant`, `Revoke`, `Checkpoint`, `Lookup`/`Keys` |
| `req/go_etcd_io_etcd_server_v3_auth.md` (3d) | `isOpPermitted` = `opErr`, `IsAdminPermitted`, `HasRole`, the admin methods with the hash, `Authenticate`, `authRecordFits` |
| `req/go_etcd_io_etcd_server_v3_storage_mvcc.md` (3e) | `Compact`, `Range`, `Rev` |
| `req/go_etcd_io_etcd_server_v3_etcdserver_api_membership.md` (2e) | `SetVersion`, `SetDowngradeInfo`, `ID`, `beView` |
| `req/go_etcd_io_etcd_server_v3_etcdserver_api_v3alarm.md` (2e, new) | `Deactivate` of an unknown type; the view's split |
| `req/go_etcd_io_etcd_server_v3_storage.md` (2e) | `Cost` exact |
| `req/go_etcd_io_etcd_api_v3_etcdserverpb.md` (3h) | `irrDecodes`, `irrMsgAt`, `reqMsgAt` |
| `req/go_etcd_io_etcd_pkg_v3_pbutil.md` (4b, new) | `MustUnmarshalMessage` |
