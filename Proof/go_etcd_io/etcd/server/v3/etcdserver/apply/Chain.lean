/-
The applier chain (`server/v3/etcdserver/apply`): its shape, what a request's run through it
can come to, and the predicate of an `applierV3` value. Lean-first (no Rocq counterpart); plan:
`notes/decisions.md`, "The server's apply". Unit 0's skeleton, finished in unit 1.

**The chain** (`Chain`): `newApplierV3` builds `auth (quota backend)` (`baseChain`);
`uberApplier.restoreAlarms` wraps it in `capped` (a `NOSPACE` alarm) and then `corrupt` (a
`CORRUPT` alarm) (`alarmChain`). Each wrapper embeds the next `applierV3` (an interface: its
methods are promoted), overriding some methods.

**The outcome** (`Outcome`, `chainStep B c rq log o`): what a request `rq` dispatched through `c`
at the log `log` comes to, by recursion on `c`, over the backend's relation `B`
(`backendStep`: the txn package's results for a KV request): `corrupt` rejects the KV requests,
compactions and lease grants and revocations (`ErrCorrupt`); `capped` rejects puts and lease
grants, and transactions that cost (`ErrNoSpace`; the cost is the quota's, opaque: either);
`auth` may reject what it checks (an auth error, before any write); `quota` passes and may turn
the backend's success into `ErrNoSpace` after the write (the write committed: `quotaApplierV3.Put`
applies first, then reports). Compaction is out of the model (`notes/decisions.md`): `B` is
`False` of it, and no triple of `applierSpec` is about it.

**The environment** (`AEnv`): the store `s` with ghost names `γ` the backend's KV is, and the
backend's batch lock: its invariant `P` and post-lock hook `f` (mvcc's `hookIs γ P f`). The apply
thread owns the store's reader slots and its sole writer at the committed log `log`, with every
lease of the state known (`kvOwn E log`); every method takes and returns it, at the log its
outcome commits (`Outcome.logAfter`). The environment's reader resource `RD` (2026-10-14, unit
A2) is the auth store's request side's (`isAuthStore st P f RD`; of the real store, a reader slot
of each of its `RWMutex`es and of the backend's read transaction, `auth.authRd st R`): the apply
thread holds one in `kvOwn` (the auth layer's KV methods' checks), the auth layer's mutex another
(its `Apply`'s admin check, which runs before the `applyFunc` gets the thread's resources).

**An applier value** (`applierSpec E c a`): the triples of the `applierV3` interface value `a`'s
methods, as the chain `c` runs them (persistent; every method but `Compaction`, which is out of
the model). The thread-owned resources a chain's methods need (`chainRes c a info`): the auth
layer's `authInfo`, holding the principal `info` (its `Apply` takes the field from its mutex,
where it holds the zero `AuthInfo` between `Apply`s, sets it to the request's principal
`principalOf rq` and hands it to the `applyFunc`, which hands it to the methods; the other layers
own nothing). The KV methods' posts state the request's class for that principal (`chainClass`,
A3 of the auth plan, 2026-10-23): if the auth layer did not reject, the permissions the request
needs were granted to it (`reqClass`, `AuthClass.lean`). Each layer's methods are `Spec/`+`Proof/`
files stated over `applierSpec E c inner` (the inner applier is a dynamic interface call); the
constructors' specs package them (`newQuotaApplierV3`: `{applierSpec E c app} … {a; applierSpec E
(.quota c) a}`).

**The errors** (2026-10-12, the merge of unit 2): every error a method returns is one `errors.Is`
can take (`applyErrIs`): the methods that leave the log say it in their triples; the KV methods'
answers name their errors (`ErrCorrupt`, `ErrNoSpace`, the txn checks' and mvcc's error
variables, `errors.New` errors by the apply package's facts `applyErrVars`; the auth store's and
the lessor's by their contracts), from which `outcomeErrIs` (`UberLemmas.lean`) derives it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

/-! ## The chain, purely -/

/-- The layers of an applier chain, outermost first. -/
inductive Chain where
  | backend
  /-- The auth layer; `on`: whether the auth store is enabled (2026-10-14, unit T1: a disabled
  store's checks pass, `isAuthStore … on`, so the layer rejects only when `on`, or for the
  requests whose rejection does not depend on the store, `authMayReject`). -/
  | auth (on : Bool) (c : Chain)
  | quota (c : Chain)
  | capped (c : Chain)
  | corrupt (c : Chain)
  deriving DecidableEq

/-- `newApplierV3`'s chain: `authApplierV3` over `quotaApplierV3` over `applierV3backend`. -/
def baseChain (on : Bool) : Chain := .auth on (.quota .backend)

/-- `restoreAlarms`' chain: the base chain, `capped` if a `NOSPACE` alarm is set, then `corrupt`
if a `CORRUPT` alarm is. -/
def alarmChain (on noSpace corrupt : Bool) : Chain :=
  let c := if noSpace then Chain.capped (baseChain on) else baseChain on
  if corrupt then .corrupt c else c

/-- The auth layer's mode of a chain (`false` if it has none; 2026-10-14, unit T1). -/
def Chain.authOn : Chain → Bool
  | .backend => false
  | .auth on c => on || c.authOn
  | .quota c => c.authOn
  | .capped c => c.authOn
  | .corrupt c => c.authOn

@[simp] theorem alarmChain_authOn (on ns cr : Bool) : (alarmChain on ns cr).authOn = on := by
  unfold alarmChain baseChain; cases on <;> cases ns <;> cases cr <;> rfl

/-- An error a layer rejects a request with, before any write. -/
inductive RejectKind where
  /-- `ErrCorrupt` (the corrupt applier). -/
  | corrupt
  /-- `ErrNoSpace` (the capped applier). -/
  | noSpace
  /-- the auth store's error (a permission check failed). -/
  | auth
  /-- the backend's own error before a write (the txn package's checks, the lessor's, ...). -/
  | backend
  deriving DecidableEq

/-- **What a request dispatched through a chain comes to** at the log `log`. -/
inductive Outcome where
  /-- An error before any write to the KV: the log unchanged. -/
  | rejected (e : RejectKind)
  /-- The backend ran: the log after it (`log'`, the txn package's commit); `noSpace`: the quota
  reports `ErrNoSpace` after the write. -/
  | applied (log' : mvcc.Log) (noSpace : Bool)

/-- The committed log after the outcome `o` at `log`. -/
def Outcome.logAfter (o : Outcome) (log : mvcc.Log) : mvcc.Log :=
  match o with
  | .rejected _ => log
  | .applied log' _ => log'

/-- The requests the corrupt applier rejects (`corrupt.go`). -/
def corruptRejects : ReqKind → Bool
  | .range | .put | .deleteRange | .txn | .compaction | .leaseGrant | .leaseRevoke => true
  | _ => false

/-- The requests the capped applier always rejects (`capped.go`; a transaction only if it
costs). -/
def cappedRejects : ReqKind → Bool
  | .put | .leaseGrant => true
  | _ => false

/-- The requests the auth applier checks in its methods (`auth.go`; the admin ones are checked
in its `Apply`, `needAdminPermission`). -/
def authChecks : ReqKind → Bool
  | .range | .put | .deleteRange | .txn | .leaseRevoke | .authUserGet | .authRoleGet => true
  | _ => false

/-- The requests the quota applier checks (`quota.go`). -/
def quotaChecks : ReqKind → Bool
  | .put | .txn | .leaseGrant => true
  | _ => false

/-- **Whether the auth layer may reject `rq`** (2026-10-14, unit T1): always if auth is enabled
(`on`); with auth disabled the store's checks pass (`IsPutPermitted`, `IsRangePermitted`,
`IsDeleteRangePermitted`, `IsAdminPermitted` return `nil`: `isAuthStore … false`), so a put, a
range, a delete or (2026-10-15, unit T2: `CheckTxnAuth` is made of those checks) a transaction is
not rejected unless it needs admin permission; the other requests' checks (a lease revocation's,
the user and role gets') are not followed. -/
def authMayReject (on : Bool) (rq : IRRModel) : Prop :=
  on = true ∨ needAdminPermission rq = true ∨
    (dispatchKind rq ≠ .put ∧ dispatchKind rq ≠ .range ∧ dispatchKind rq ≠ .deleteRange ∧
      dispatchKind rq ≠ .txn ∧ dispatchKind rq ≠ .leaseRevoke)

/-- **The outcome relation** of the chain `c` on `rq` at `log`, over the backend's `B`. -/
def chainStep (B : IRRModel → mvcc.Log → Outcome → Prop) :
    Chain → IRRModel → mvcc.Log → Outcome → Prop
  | .backend, rq, log, o => B rq log o
  | .corrupt c, rq, log, o =>
      if corruptRejects (dispatchKind rq) then o = .rejected .corrupt
      else chainStep B c rq log o
  | .capped c, rq, log, o =>
      if cappedRejects (dispatchKind rq) then o = .rejected .noSpace
      else if dispatchKind rq = .txn then o = .rejected .noSpace ∨ chainStep B c rq log o
      else chainStep B c rq log o
  | .auth on c, rq, log, o =>
      if authChecks (dispatchKind rq) ∨ needAdminPermission rq = true then
        (authMayReject on rq ∧ o = .rejected .auth) ∨ chainStep B c rq log o
      else chainStep B c rq log o
  -- the quota layer: the inner outcome. The backend never reaches its quota (the disk never
  -- fills: `isQuota`'s `Available` returns `true`, a construction premise; 2026-10-14, unit T1),
  -- so `quotaApplierV3` never sets `ErrNoSpace` (it would only have set it on the response of a
  -- write already applied, `quota.go:36-42`).
  | .quota c, rq, log, o => chainStep B c rq log o

/-! ## The backend's relation -/

/-- **What the backend applier does with `rq` at the sole writer's log `log`** (the txn package's
results, `backend.go`): a put is the txn package's `Put` (the lease not found or, with an ignore
flag, the key missing: rejected; else, the key found if an ignore flag needs it, the one change
`putChangeOf` committed); a delete the filter (`delChanges` committed: the apply thread's context
is never done, so the `PrevKv` range read does not fail); a range reads `log`; a transaction is
`checkTxn`'s error (for a plain transaction, `txn.txnPlain`, only when a put of its path does not
find the previous key-value it needs) or, every such put finding it (`PathsIgnOk`), the server's
run `srvRunTxn` committed (nothing for a read-only one); a revocation commits the lessor's
deletions of the lease's keys; the other requests do not touch the KV (applied, or the
component's error). A compaction leaves the log as it is (M2's apply side, 2026-10-31: until then
out of the model, `False`; the store compacts its index, changing no value at a revision it
keeps); a request with no field set is out of the model (`dispatch` panics). 2026-10-15 (unit T2): the put's, the delete's and the transaction's cases
made exact, so that the KV model is a function of the state (`KVModelDefs.lean`). -/
def backendStep (rq : IRRModel) (log : mvcc.Log) (o : Outcome) : Prop :=
  match dispatchKind rq with
  | .put => ∃ op, rq.put = some op ∧
      ((op.leaseID ≠ W64 0 ∧ o = .rejected .backend) ∨
       (txn.needsPrev op = true ∧ mvcc.findKey op.key (mvcc.stateAfter log) = none ∧
         o = .rejected .backend) ∨
       ((txn.needsPrev op = true → (mvcc.findKey op.key (mvcc.stateAfter log)).isSome) ∧
        o = .applied (log ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter log))]])
         false))
  | .deleteRange => ∃ op, rq.deleteRange = some op ∧
      o = .applied (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) op)) false
  | .range => o = .applied log false
  | .txn => ∃ t, rq.txn = some t ∧
      ((o = .rejected .backend ∧
          (txn.txnPlain t → ¬ txn.PathsIgnOk (mvcc.stateAfter log)
            (t.branch (txn.txnOk (mvcc.stateAfter log) t)))) ∨
       (o = .applied (mvcc.commitLog log
           (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) false ∧
        (txn.txnReadonly t = true →
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 = []) ∧
        txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t))))
  | .leaseRevoke => ∃ id, rq.leaseRevoke = some id ∧ o = .applied (revokeLog log id) false
  | .compaction => o = .applied log false
  | .none => False
  | _ => o = .applied log false ∨ o = .rejected .backend

/-! ## The per-request premises -/

/-- A put's premise at the sole writer's log: room for one more revision. -/
def putOk (log : mvcc.Log) : Prop := log.length + 4 ≤ 2 ^ 63

/-- A delete's premise: room for one more revision. (Until D19c's move, 2026-10-18, also fewer
than `2 ^ 56` keys in the request's range, the real backend's bound on a session's puts: the
store's write transaction now has it by its time receipts, `mvcc.storeTxnWriteIs_small`.) -/
def delOk (log : mvcc.Log) (_o : OpFull) : Prop :=
  log.length + 4 ≤ 2 ^ 63

/-- A range's premises: room for the read, a valid sort target, the sort's premise. -/
def rangeOk (log : mvcc.Log) (o : OpFull) : Prop :=
  log.length + 3 ≤ 2 ^ 63 ∧ txn.validSortTarget o ∧ txn.sortOk o log

/-- **A lease grant the apply thread admits** (the lease-grant plan's D3, 2026-11-02; since its B1/B2
commit 2 `rqOk`'s grant arm in a cluster that grants leases): a request dispatched to `LeaseGrant`,
with no admin and no side-effect-free field set (the server proposes `{LeaseGrant: r}` alone), its
id not `0` (`EtcdServer.LeaseGrant` writes a fresh id while `r.ID` is `0`,
`v3_server.go:436-439`). Nothing about the TTL or the live set: `lessor.Grant` answers an error
for a TTL above `MaxLeaseTTL` or a live id, which the response carries (with the lessor tied to
the KV model's lease table, the outcome is a function of the applied log). -/
def grantKindOk (rq : IRRModel) : Prop :=
  dispatchKind rq = .leaseGrant ∧ needAdminPermission rq = false ∧ noSideEffect rq = false ∧
    ∀ g, rq.leaseGrant = some g → g.id ≠ W64 0

/-- **A lease revocation the apply thread admits** (the lease-expiry plan's X7, 2026-11-04): a
request dispatched to `LeaseRevoke`, with no admin and no side-effect-free field set (the server
proposes `{LeaseRevoke: r}` alone, `v3_server.go`'s `LeaseRevoke`). -/
def revokeKindOk (rq : IRRModel) : Prop :=
  dispatchKind rq = .leaseRevoke ∧ needAdminPermission rq = false ∧ noSideEffect rq = false

/-- **The per-request premise** of `rq` at the sole writer's log `log`, by what `dispatch` does
with it: the txn package's for a KV request (`TxnPre` for a transaction); a lease checkpoint
request with at most one checkpoint (each checkpoint is its own critical section of the batch
lock: `nonissues/etcd-apply-lease-checkpoint-sections.md`; until 2026-10-17); a cluster version that
parses and is not above the server's (`semverAtMostServer`, the cluster-rows stage, 2026-11-02:
`isCluster`'s `SetVersion` row panics above it). **No lease request** (D14h, 2026-10-17, the user's decision): the workload has no
`LeaseGrant`, `LeaseRevoke` or `LeaseCheckpoint` (with no lease granted none expires, so the
lessor proposes no revocation and no checkpoint); `lessor.Revoke` is not specified (unit T3).
**No alarm, auth or downgrade request** (D22, 2026-10-23: the backend over every bucket): their
writers take the environment's write right `AEnv.RW` (the server's is `False`: the apply thread
holds the rest buckets at their model, `RestModel.lean`), so `dispatch` does not call them; no
workload admits one (the server's `plainCover`). Until then their premise was `True` (the user's
and role's name within the key bound for `UserAdd`/`RoleAdd`). (The lease-grant stage, B1,
2026-11-02, the user's decision: in place, gated) In a cluster that grants leases (`lg`,
`KVNames.lg`), a grant the apply thread admits (`grantKindOk`); in one that grants none, no grant,
as before (`rqOk_false_leaseGrant`), so `rqOk .none` means what `rqOk` meant until then. (X7 option
(iii), 2026-11-04) Indexed by the cluster's lease mode `lm` (`KVNames.lm`), the grant arm at
`lm ≠ .none`. -/
def rqOk (lm : lease.Mode) (log : mvcc.Log) (rq : IRRModel) : Prop :=
  match dispatchKind rq with
  | .put => putOk log
  | .deleteRange => ∀ o, rq.deleteRange = some o → delOk log o
  | .range => ∀ o, rq.range = some o → rangeOk log o
  | .txn => ∀ t, rq.txn = some t → txn.TxnPre log t
  | .leaseGrant => match lm with
    | .none => False
    | _ => grantKindOk rq
  | .leaseRevoke => match lm with
    | .revocable => revokeKindOk rq ∧ putOk log
    | _ => False
  | .leaseCheckpoint => False
  | .clusterVersionSet => ∀ v, rq.clusterVersionSet = some v → semverValid v ∧ semverAtMostServer v
  | .downgradeInfoSet => False
  | .alarm => False
  | .authenticate => False
  | .authEnable => False
  | .authDisable => False
  | .authUserAdd => False
  | .authUserDelete => False
  | .authUserChangePassword => False
  | .authUserGrantRole => False
  | .authUserGet => False
  | .authUserRevokeRole => False
  | .authRoleAdd => False
  | .authRoleGrantPermission => False
  | .authRoleGet => False
  | .authRoleRevokePermission => False
  | .authRoleDelete => False
  | .authUserList => False
  | .authRoleList => False
  | _ => True

/-- **The rest state's premise of `dispatch(rq)`** (the cluster-rows stage, 2026-11-02): a member
attributes request's member is a member of the in-memory members (`UpdateAttributes` panics on an
id that is neither a member nor removed, and the server removes no member). Of the request's model
and the rest state the entry meets: the apply thread's `restModel`, which the server's proof
relates to the committed log's workload facts (`attrLogOk`). -/
def restReqOk (rq : IRRModel) (rs : RestM) : Prop :=
  dispatchKind rq = .clusterMemberAttrSet →
    ∀ a, rq.clusterMemberAttrSet = some a → (rs.mem.lookup a.memberID).isSome = true

/-- Another request kind asks nothing of the rest state. -/
theorem restReqOk_other (rq : IRRModel) (rs : RestM) (h : dispatchKind rq ≠ .clusterMemberAttrSet) :
    restReqOk rq rs := fun hk => absurd hk h

/-- **`dispatch`'s `ClusterMemberAttrSet` call site**. -/
theorem restReqOk_attr (rq : IRRModel) (rs : RestM) (a : MemberAttrModel) (h : restReqOk rq rs)
    (hk : dispatchKind rq = .clusterMemberAttrSet) (ha : rq.clusterMemberAttrSet = some a) :
    (rs.mem.lookup a.memberID).isSome = true := h hk a ha

/-- **The admin requests admitted in the mode `on`** (the auth plan's E2m, continued): their shape
only, the names within bbolt's key bound (the step specs' premise; the fuel bounds the rest,
`AuthFuel.lean`). `SetUp`'s five: `UserAdd`, `RoleAdd`, `UserGrantRole`, `RoleGrantPermission`
(whose names the request model records since E2n) and `AuthEnable`; not the other admin kinds.
A `UserAdd`'s password choice cannot fail (`UserAddModel.pwSure`, the server's own form, which
`EtcdServer.UserAdd` proposes: E2x), so its outcome is the step's alone (E3a). (C1's A2,
2026-10-28) And `Authenticate`, which writes nothing (`GetUser` only reads its name: no key bound),
in a request needing no admin permission (`needAdminPermission` reads the request's fields, the
dispatch its first: a request with an admin field beside it would pass the admin check and still
dispatch `Authenticate`; the server proposes it alone), its token prefix one the provider makes
(`auth.tokPrefixOk`, 2026-10-30: no space, so a token's `"Bearer "` trim leaves it as issued). -/
def adminKindOk (rq : IRRModel) : Prop :=
  match dispatchKind rq with
  | .authUserAdd => ∀ m, rq.authUserAdd = some m → m.name.length ≤ backend.maxKeySize ∧ m.pwSure
  | .authRoleAdd => ∀ n, rq.authRoleAdd = some n → n.length ≤ backend.maxKeySize
  | .authUserGrantRole => ∀ u ro, rq.authUserGrantRole = some (u, ro) → u.length ≤ backend.maxKeySize
  | .authRoleGrantPermission =>
      ∀ n w, rq.authRoleGrantPermission = some (n, w) → n.length ≤ backend.maxKeySize
  | .authEnable => True
  | .authenticate => needAdminPermission rq = false ∧
      ∀ am, rq.authenticate = some am → auth.tokPrefixOk am.simpleToken
  | _ => False

/-- **The per-request premise in the auth mode `M`** (E2m, continued): `rqOk`, or, in the mode `on`
only, an admitted admin request (`adminKindOk`). A second clause rather than a mode-indexed
`rqOk`: `rqOk` and every statement written with it (the entries' claims, the examples' workloads)
keep their text, and in the mode `off` the two agree (`rqOkM_off`). -/
def rqOkM (M : auth.AuthMode) (log : mvcc.Log) (rq : IRRModel) : Prop :=
  rqOk .none log rq ∨ (M.isOn = true ∧ adminKindOk rq)

theorem rqOkM_off (log : mvcc.Log) (rq : IRRModel) : rqOkM .off log rq ↔ rqOk .none log rq := by
  simp [rqOkM, auth.AuthMode.isOn]

theorem rqOkM_of_rqOk (M : auth.AuthMode) (log : mvcc.Log) (rq : IRRModel)
    (h : rqOk .none log rq) : rqOkM M log rq := Or.inl h

/-- **A cluster that grants none admits no grant** (the lease-grant plan's B1/B2 commit 2): `rqOk
false`'s grant arm is `False`, every other arm `rqOk lg`'s whatever `lg`. -/
theorem rqOk_false_leaseGrant (log : mvcc.Log) (rq : IRRModel)
    (hk : dispatchKind rq = .leaseGrant) : ¬ rqOk .none log rq := by
  simp [rqOk, hk]

/-- **What a cluster that grants none admits, one that grants does** (`rqOk` is monotone in `lg`). -/
theorem rqOk_of_false (lm : lease.Mode) (log : mvcc.Log) (rq : IRRModel) (h : rqOk .none log rq) :
    rqOk lm log rq := by
  unfold rqOk at h ⊢
  split <;> simp_all

/-- **A grant is admitted only where the cluster grants** (`rqOk`'s grant arm). -/
theorem rqOk_leaseGrant (lm : lease.Mode) (log : mvcc.Log) (rq : IRRModel)
    (hk : dispatchKind rq = .leaseGrant) : rqOk lm log rq ↔ lm ≠ .none ∧ grantKindOk rq := by
  cases lm <;> simp [rqOk, hk]

/-- **A revocation is admitted only at the revocable mode** (`rqOk`'s revocation arm; the lease-expiry
plan's X7). -/
theorem rqOk_leaseRevoke (lm : lease.Mode) (log : mvcc.Log) (rq : IRRModel)
    (hk : dispatchKind rq = .leaseRevoke) :
    rqOk lm log rq ↔ lm = .revocable ∧ revokeKindOk rq ∧ putOk log := by
  cases lm <;> simp [rqOk, hk]

/-! ## The compaction arm, pure (M2, the apply side, 2026-10-31) -/

/-- **The chains whose `Compaction` reaches the backend**: the auth, quota and capped wrappers pass
it on (they do not override it), the corrupt applier answers `ErrCorrupt` (`corrupt.go`). -/
def chainCompacts : Chain → Bool
  | .backend => true
  | .auth _ c => chainCompacts c
  | .quota c => chainCompacts c
  | .capped c => chainCompacts c
  | .corrupt _ => false

/-- **The compaction revision after `Compact(rev)`** at `crev` (`updateCompactRev`): `rev` when
above, else unchanged (`ErrCompacted`). -/
def cmpRevAfter (crev : Int) (rev : w64) : Int :=
  if crev < sint.Z rev then sint.Z rev else crev

theorem cmpRevAfter_ge (crev : Int) (rev : w64) : crev ≤ cmpRevAfter crev rev := by
  unfold cmpRevAfter; split <;> omega

/-- **What a compaction at `rev` needs at the log `log`** (pure; written once, review round 1's
S-8): the store compacting (its backend in compaction mode: the KV invariant admits compaction
entries only in the cluster's compaction mode, and `envAgree`/`srvEnvOkD` tie the store's mode to
it) and the revision one of the log's (the committed log's claim, `cmpLogOk`). No `NoDelPutAt`:
the fork has etcd-io/etcd#22377 (review round 1's F-5; mvcc's specs drop the premise before the
switch). (F2, stage 2; the user's Q7, approved 2026-11-03) The revision at least `1`: the store's
compaction's scope restriction (`store.Compact.spec`, `nonissues/etcd-restore-scheduled-compact-zero.md`),
which the server's `EtcdServer.Compact.spec` (`1 ≤ r`) supplies. -/
def cmpAdmitRev (kb : Option mvcc.KBReal) (log : mvcc.Log) (rev : w64) : Prop :=
  mvcc.kbCmpM kb ∧ sint.Z rev < log.length ∧ 1 ≤ sint.Z rev

theorem chainCompacts_auth (on : Bool) (c : Chain) : chainCompacts (.auth on c) = chainCompacts c := rfl
theorem chainCompacts_quota (c : Chain) : chainCompacts (.quota c) = chainCompacts c := rfl
theorem chainCompacts_capped (c : Chain) : chainCompacts (.capped c) = chainCompacts c := rfl


/-! ## A grant's outcome (the lease-grant stage, 2.0; from `GrantRest.lean`) -/

/-- **The chain lets a grant through to the backend**: no capped and no corrupt layer (each
rejects a grant: `cappedRejects`, `corruptRejects`). -/
def grantGoes : Chain → IRRModel → Bool
  | .backend, _ => true
  | .auth _ c, rq => grantGoes c rq
  | .quota c, rq => grantGoes c rq
  | .capped _, _ => false
  | .corrupt _, _ => false

/-- **The live set after the outcome `o`** of `rq` dispatched with `v3`: a grant applied appends
its id. Only a request dispatched as a grant (`dispatchKind`) with `v3` (the lease-grant plan's
Freeze, amendment (B)): without `v3`, `dispatch` returns `.applied` without calling the chain
(`dispatchStep`), and a request whose first set field is another keeps its stray `LeaseGrant`
field unread; both leave the live set, as `dispatchTable`. -/
def grantIds (rq : IRRModel) (v3 : Bool) (o : Outcome) (L : List w64) : List w64 :=
  if dispatchKind rq = .leaseGrant ∧ v3 = true then
    match o, rq.leaseGrant with
    | .applied .., some g => L ++ [g.id]
    | _, _ => L
  else L

/-- **The rest buckets after the outcome `o`** of `rq` dispatched with `v3`, the record at the TTL
`t` (a request dispatched as a grant with `v3` only, as `grantIds`). -/
def grantRest (t : w64) (rq : IRRModel) (v3 : Bool) (o : Outcome) (r : RestM) : RestM :=
  if dispatchKind rq = .leaseGrant ∧ v3 = true then
    match o, rq.leaseGrant with
    | .applied .., some g => restGrantT g.id t r
    | _, _ => r
  else r

theorem grantIds_rejected (rq : IRRModel) (v3 : Bool) (e : RejectKind) (L : List w64) :
    grantIds rq v3 (.rejected e) L = L := by
  unfold grantIds; split <;> rfl

theorem grantRest_rejected (t : w64) (rq : IRRModel) (v3 : Bool) (e : RejectKind) (r : RestM) :
    grantRest t rq v3 (.rejected e) r = r := by
  unfold grantRest; split <;> rfl

/-- No grant field: the identity. -/
theorem grantIds_none (rq : IRRModel) (v3 : Bool) (o : Outcome) (L : List w64)
    (h : rq.leaseGrant = none) : grantIds rq v3 o L = L := by
  unfold grantIds; cases o <;> simp [h]

theorem grantRest_none (t : w64) (rq : IRRModel) (v3 : Bool) (o : Outcome) (r : RestM)
    (h : rq.leaseGrant = none) : grantRest t rq v3 o r = r := by
  unfold grantRest; cases o <;> simp [h]

/-- A request not dispatched as a grant: the identity. -/
theorem grantIds_nonGrant (rq : IRRModel) (v3 : Bool) (o : Outcome) (L : List w64)
    (h : dispatchKind rq ≠ .leaseGrant) : grantIds rq v3 o L = L := by
  unfold grantIds; rw [if_neg (fun h' => h h'.1)]

theorem grantRest_nonGrant (t : w64) (rq : IRRModel) (v3 : Bool) (o : Outcome) (r : RestM)
    (h : dispatchKind rq ≠ .leaseGrant) : grantRest t rq v3 o r = r := by
  unfold grantRest; rw [if_neg (fun h' => h h'.1)]

/-- **The live set after the outcome `o`** of `rq` dispatched with `v3`, for a revocation (the
lease-expiry plan's X7, the user's decision of 2026-11-04: the post names the outcome): an applied
revocation of `id` drops it (whether it was live or not: not live, the filter keeps the set); a
rejection, or a request not dispatched as a revocation with `v3`, keeps it, as `grantIds`. -/
def revokeIds (rq : IRRModel) (v3 : Bool) (o : Outcome) (L : List w64) : List w64 :=
  if dispatchKind rq = .leaseRevoke ∧ v3 = true then
    match o, rq.leaseRevoke with
    | .applied .., some id => L.filter (· != id)
    | _, _ => L
  else L

/-- **The rest buckets after the outcome `o`** of a revocation dispatched with `v3`, the live set
before it `T`: an applied revocation of a live lease deletes its record (`restRevoke`); of one not
live (the lessor's `ErrLeaseNotFound`), nothing. -/
def revokeRest (T : List w64) (rq : IRRModel) (v3 : Bool) (o : Outcome) (r : RestM) : RestM :=
  if dispatchKind rq = .leaseRevoke ∧ v3 = true then
    match o, rq.leaseRevoke with
    | .applied .., some id => if id ∈ T then restRevoke id r else r
    | _, _ => r
  else r

theorem revokeIds_rejected (rq : IRRModel) (v3 : Bool) (e : RejectKind) (L : List w64) :
    revokeIds rq v3 (.rejected e) L = L := by
  unfold revokeIds; split <;> rfl

theorem revokeRest_rejected (T : List w64) (rq : IRRModel) (v3 : Bool) (e : RejectKind)
    (r : RestM) : revokeRest T rq v3 (.rejected e) r = r := by
  unfold revokeRest; split <;> rfl

/-- A request not dispatched as a revocation: the identity. -/
theorem revokeIds_nonRevoke (rq : IRRModel) (v3 : Bool) (o : Outcome) (L : List w64)
    (h : dispatchKind rq ≠ .leaseRevoke) : revokeIds rq v3 o L = L := by
  unfold revokeIds; rw [if_neg (fun h' => h h'.1)]

theorem revokeRest_nonRevoke (T : List w64) (rq : IRRModel) (v3 : Bool) (o : Outcome) (r : RestM)
    (h : dispatchKind rq ≠ .leaseRevoke) : revokeRest T rq v3 o r = r := by
  unfold revokeRest; rw [if_neg (fun h' => h h'.1)]

theorem revokeIds_noV3 (rq : IRRModel) (o : Outcome) (L : List w64) :
    revokeIds rq false o L = L := by
  unfold revokeIds; rw [if_neg (fun h' => Bool.false_ne_true h'.2)]

theorem revokeRest_noV3 (T : List w64) (rq : IRRModel) (o : Outcome) (r : RestM) :
    revokeRest T rq false o r = r := by
  unfold revokeRest; rw [if_neg (fun h' => Bool.false_ne_true h'.2)]

/-- An applied revocation of `id`. -/
theorem revokeIds_applied (rq : IRRModel) (id : w64) (l : mvcc.Log) (ns : Bool) (L : List w64)
    (hk : dispatchKind rq = .leaseRevoke) (hs : rq.leaseRevoke = some id) :
    revokeIds rq true (.applied l ns) L = L.filter (· != id) := by
  unfold revokeIds; rw [if_pos ⟨hk, rfl⟩, hs]

theorem revokeRest_applied (T : List w64) (rq : IRRModel) (id : w64) (l : mvcc.Log) (ns : Bool)
    (r : RestM) (hk : dispatchKind rq = .leaseRevoke) (hs : rq.leaseRevoke = some id) :
    revokeRest T rq true (.applied l ns) r = if id ∈ T then restRevoke id r else r := by
  unfold revokeRest; rw [if_pos ⟨hk, rfl⟩, hs]

/-- Without `v3` (`dispatch` does not call the chain): the identity. -/
theorem grantIds_noV3 (rq : IRRModel) (o : Outcome) (L : List w64) :
    grantIds rq false o L = L := by
  unfold grantIds; rw [if_neg (fun h' => Bool.false_ne_true h'.2)]

theorem grantRest_noV3 (t : w64) (rq : IRRModel) (o : Outcome) (r : RestM) :
    grantRest t rq false o r = r := by
  unfold grantRest; rw [if_neg (fun h' => Bool.false_ne_true h'.2)]

/-- An outcome that is not `.applied`: the identity. -/
theorem grantIds_not_applied (rq : IRRModel) (v3 : Bool) (o : Outcome) (L : List w64)
    (h : ∀ log' ns, o ≠ .applied log' ns) : grantIds rq v3 o L = L := by
  cases o with
  | rejected => exact grantIds_rejected _ _ _ _
  | applied log' ns => exact absurd rfl (h log' ns)

theorem grantRest_not_applied (t : w64) (rq : IRRModel) (v3 : Bool) (o : Outcome) (r : RestM)
    (h : ∀ log' ns, o ≠ .applied log' ns) : grantRest t rq v3 o r = r := by
  cases o with
  | rejected => exact grantRest_rejected _ _ _ _ _
  | applied log' ns => exact absurd rfl (h log' ns)

theorem grantIds_applied (rq : IRRModel) (g : LeaseGrantModel) (log' : mvcc.Log) (ns : Bool)
    (L : List w64) (hk : dispatchKind rq = .leaseGrant) (h : rq.leaseGrant = some g) :
    grantIds rq true (.applied log' ns) L = L ++ [g.id] := by
  unfold grantIds; rw [if_pos ⟨hk, rfl⟩, h]

theorem grantRest_applied (t : w64) (rq : IRRModel) (g : LeaseGrantModel) (log' : mvcc.Log)
    (ns : Bool) (r : RestM) (hk : dispatchKind rq = .leaseGrant) (h : rq.leaseGrant = some g) :
    grantRest t rq true (.applied log' ns) r = restGrantT g.id t r := by
  unfold grantRest; rw [if_pos ⟨hk, rfl⟩, h]

theorem grantRest_mem (t : w64) (rq : IRRModel) (v3 : Bool) (o : Outcome) (r : RestM) :
    (grantRest t rq v3 o r).mem = r.mem := by
  unfold grantRest; split
  · split <;> rfl
  · rfl

/-- **A grant's outcome is the lessor's verdict** (the lease-grant plan's Freeze, amendment (C),
the user's, 2026-11-03): for `rq` dispatched as the grant `g` with `v3`, the outcome `o` is
applied exactly when the chain `c` lets the grant through (`grantGoes`) and the lessor's condition
holds at the live set `T` (`grantIdsOk`); vacuous for any other request or without `v3`.
`dispatch.spec`'s and `Apply.spec`'s posts carry it, so the server's table (`dispatchTable`) follows
the live set (`grantIds`). -/
def grantOutOk (c : Chain) (rq : IRRModel) (v3 : Bool) (T : List w64) (o : Outcome) : Prop :=
  dispatchKind rq = .leaseGrant → v3 = true → ∀ g : LeaseGrantModel, rq.leaseGrant = some g →
    ((∃ l ns, o = .applied l ns) ↔ grantGoes c rq = true ∧ grantIdsOk T g.id g.ttl)

theorem grantOutOk_nonGrant (c : Chain) (rq : IRRModel) (v3 : Bool) (T : List w64) (o : Outcome)
    (h : dispatchKind rq ≠ .leaseGrant) : grantOutOk c rq v3 T o :=
  fun hk => absurd hk h

theorem grantOutOk_noV3 (c : Chain) (rq : IRRModel) (T : List w64) (o : Outcome) :
    grantOutOk c rq false T o :=
  fun _ h => absurd h Bool.false_ne_true

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The environment and the thread's resources -/

/-- **A chain's environment**: the store `s` (ghost names `γ`) the backend's KV is, its
backend's batch lock's invariant `P` and post-lock hook `f`, the auth store's reader resource
`RD` (see the file header); `γrev`, the ghost map of the
revisions' tokens the server's apply thread mints as the KV's log grows (the clients'
`etcdRevToken`, the vertical slice's unit V1: `InvRequest.lean`, `revTok`), which the apply package
does not use. -/
structure AEnv (GF : BundledGFunctors) where
  s : Loc
  γ : mvcc.StoreNames
  P : IProp GF
  f : val
  RD : IProp GF
  γrev : GName
  /-- the auth store's mode (2026-10-14, unit T1, a boolean; 2026-10-23, the auth plan's A0,
  `auth.AuthMode`): the auth store's contract's (`isAuthStore … E.authMode`); the auth layer's
  boolean mode (`Chain.auth E.authOn`) is `E.authOn`, whether it may refuse -/
  authMode : auth.AuthMode
  /-- the apply thread's right to `ForceSnapshot` (D14i, 2026-10-17: the server's
  `s.forceDiskSnapshot`, which `ForceSnapshot` writes), threaded to the cluster methods -/
  FS : IProp GF
  /-- the apply thread's resources `ConsistentIndex` reads under (D14i: the server's apply
  protocol's state with the consistent index's owner share), lent out of the critical section's
  precondition (`ciSplit`), with the value `ConsistentIndex` returns under each (`ciC C x`: under
  `C` it returns `x`; C1's A2, 2026-10-28: the authenticate request's token index) -/
  ciC : IProp GF → w64 → Prop
  /-- (D22, 2026-10-23: the backend over every bucket) the apply thread's resource of the rest
  buckets and the cluster's in-memory members at their value (`RestModel.lean`): the cluster's
  `SetVersion` and `UpdateAttributes` change it (`isCluster`) -/
  RO : RestM → IProp GF
  /-- (D22, 2026-10-23) the write right of the writers the workload does not reach (the alarm
  store's, the auth store's, the lessor's, the cluster's `SetDowngradeInfo`); the server's is
  `False` -/
  RW : IProp GF
  /-- (D22 receiver epochs, S7b, 2026-10-23) the server's ghost variable of its current backend
  (`s.be`'s, `bemuP`), which the apply package does not use (as `γrev`) -/
  γbe : GName
  /-- (M2, the storage side, 2026-10-30: review round 2's N1, the approval's item 9) the server's
  compaction mode: whether its store compacts (the auto-compactor on), which `envAgree` ties to the
  store's logical mode (`E.γ.cm`) and the stand-in `E₀` carries to the examples; the apply package
  does not use it (as `γrev`) -/
  cmp : Bool := false
  /-- (C3's server stage, 2026-11-02) the cluster's compaction retention (`KVNames.cret`, which
  `srvKVInvs` ties it to): what the server's compactor's proposals must keep (`cret ≤` its
  retention, `compactableOk_server`); the apply package does not use it -/
  cret : Nat := 0
  /-- (the lease-grant stage, B1, 2026-11-02) whether the cluster grants leases (`KVNames.lg`, which
  `srvKVInvs` ties it to): the per-request premise admits a grant only then (`rqOk`); the apply
  package does not read it until its chain passes it to `rqOk` (commit 4 of the lease-grant plan's
  last section; the lease-expiry plan's X7 option (iii), 2026-11-04: the field is the cluster's lease
  mode `lm`, `AEnv.lg` its grant flag) -/
  lm : lease.Mode := .none
  /-- (the lease-grant stage, 2.0, 2026-11-03) the ghost variable of the lessor's live set, whose
  halves the apply thread's image (`srvRest`) and its KV resources (`kvOwn`'s `leasesLive`) hold in
  a cluster that grants leases (`ltHalf`); unused otherwise -/
  γlt : GName := default

omit package_sem in
/-- **Whether the cluster grants leases** (the lease-expiry plan's X7 option (iii), 2026-11-04: until
then the field `lg`): its lease mode is not `none`. -/
@[reducible] def AEnv.lg (E : AEnv GF) : Bool := decide (E.lm ≠ .none)

omit package_sem in
theorem AEnv.lg_eq (E : AEnv GF) : E.lg = decide (E.lm ≠ .none) := rfl

omit package_sem in
theorem AEnv.lm_of_lg_false {E : AEnv GF} (h : E.lg = false) : E.lm = .none := by
  simpa [AEnv.lg_eq] using h
omit package_sem in
theorem AEnv.lm_of_lg_true {E : AEnv GF} (h : E.lg = true) : E.lm ≠ .none := by
  simpa [AEnv.lg_eq] using h
omit package_sem in
theorem AEnv.lg_false_of_lm {E : AEnv GF} (h : E.lm = .none) : E.lg = false := by
  simp [AEnv.lg_eq, h]
omit package_sem in
theorem AEnv.lg_true_of_lm {E : AEnv GF} (h : E.lm ≠ .none) : E.lg = true := by
  simpa [AEnv.lg_eq] using h

/-- Whether the auth store may refuse (`Chain.auth E.authOn`; until the auth plan's A0 a field):
`false` exactly in the mode `off`. -/
def AEnv.authOn (E : AEnv GF) : Bool := E.authMode.isOn

theorem AEnv.authOn_eq (E : AEnv GF) : E.authOn = E.authMode.isOn := rfl

/-- **The apply thread's half of the lessor's live set `L`** (the lease-grant stage, 2.0,
2026-11-03): in a cluster that grants leases (`E.lg`), half of `E.γlt` at `L`; `True` otherwise
(`ltHalf_false`). Its two holders tie the image's lease records to the lessor's live set. -/
def ltHalf (E : AEnv GF) (L : List w64) : IProp GF :=
  if E.lg then ghostVar E.γlt (1 : Qp).half L else iprop(True)

theorem ltHalf_false (E : AEnv GF) (L : List w64) (h : E.lg = false) :
    ltHalf E L = iprop(True) := by
  unfold ltHalf; rw [h]; rfl

open Iris.ProofMode in
/-- The two halves agree (in a cluster that grants leases). -/
theorem ltHalf_agree (E : AEnv GF) (L T : List w64) (h : E.lg = true) :
    ltHalf E L ∗ ltHalf E T ⊢ ⌜L = T⌝ := by
  unfold ltHalf; simp only [h, ↓reduceIte]
  iintro ⟨H1, H2⟩
  ihave %Heq := ghostVar_agree E.γlt L (1 : Qp).half T (1 : Qp).half $$ H1 H2
  ipureintro; exact Heq

open Iris.ProofMode in
/-- The two halves together update the live set. -/
theorem ltHalf_update (E : AEnv GF) (L T L' : List w64) :
    ⊢ ltHalf E L -∗ ltHalf E T ==∗ ltHalf E L' ∗ ltHalf E L' := by
  unfold ltHalf
  cases h : E.lg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro - - !>
    isplitl <;> itrivial
  · simp only [↓reduceIte]
    exact ghostVar_update_halves (GF := GF) L' E.γlt L T

/-- **The apply thread's half of the ids the lessor ever had, `U`** (the lease-expiry plan's E3 (c),
2026-11-05): in a cluster that grants leases (`E.lg`), `lease.leaseEver E.γ.leases U`; `True`
otherwise. `dispatch` and `Apply` take it and give it back with an applied grant's id added
(`grantIds`). -/
def everOwn (E : AEnv GF) (U : List w64) : IProp GF :=
  if E.lg then lease.leaseEver E.γ.leases U else iprop(True)

omit package_sem in
theorem everOwn_false (E : AEnv GF) (U : List w64) (h : E.lg = false) :
    everOwn E U = iprop(True) := by
  unfold everOwn; rw [h]; rfl

omit package_sem in
theorem everOwn_true (E : AEnv GF) (U : List w64) (h : E.lg = true) :
    everOwn E U = lease.leaseEver E.γ.leases U := by
  unfold everOwn; rw [h]; rfl

omit package_sem in
theorem everOwn_of_lg (E : AEnv GF) (U : List w64) (h : E.lg = true) :
    everOwn E U ⊢ lease.leaseEver E.γ.leases U := by
  rw [everOwn_true E U h]

omit package_sem in
theorem everOwn_to_lg (E : AEnv GF) (U : List w64) (h : E.lg = true) :
    lease.leaseEver E.γ.leases U ⊢ everOwn E U := by
  rw [everOwn_true E U h]

/-- **A request's grant id is new to `U`, unless the lessor is monotone** (E3 (c); persistent):
for a request dispatched as the grant `g`, the lessor monotone or `g.id ∉ U` (what
`lease.lessor.Grant.spec` takes); nothing for another kind. -/
def grantFresh (E : AEnv GF) (rq : IRRModel) (U : List w64) : IProp GF :=
  iprop(□ (⌜dispatchKind rq = .leaseGrant⌝ → ∀ g : LeaseGrantModel, ⌜rq.leaseGrant = some g⌝ →
    lease.lessorModeIs E.γ.leases true ∨ ⌜g.id ∉ U⌝))

instance grantFresh_persistent (E : AEnv GF) (rq : IRRModel) (U : List w64) :
    Persistent (grantFresh (GF := GF) E rq U) := by
  unfold grantFresh; infer_instance

omit package_sem in
open Iris.ProofMode in
theorem grantFresh_of_not_grant (E : AEnv GF) (rq : IRRModel) (U : List w64)
    (h : dispatchKind rq ≠ .leaseGrant) : ⊢ grantFresh (GF := GF) E rq U := by
  iunfold grantFresh
  iintro !> %hk
  exact absurd hk h

/-- **A fresh response header's four id fields owned** (2.11a, 2026-11-03): `ClusterId`, `MemberId`,
`RaftTerm`, `LeaderId` at the header `h`, any values (`txn.respHdrOwn`'s body). -/
def hdrFields (h : Loc) : IProp GF :=
  iprop(∃ (c m t l : w64),
    structFieldRef etcdserverpb.ResponseHeader go!"ClusterId" h ↦ c ∗
    structFieldRef etcdserverpb.ResponseHeader go!"MemberId" h ↦ m ∗
    structFieldRef etcdserverpb.ResponseHeader go!"RaftTerm" h ↦ t ∗
    structFieldRef etcdserverpb.ResponseHeader go!"LeaderId" h ↦ l)

/-- **The live leases of the state `s`** (2026-10-13, unit 8 of the backend): the lease owner's
resource at some live set `L` (its half of the lessor's live set, a reader slot of its lock) of
which every lease of `s` is; (unit T3, L2b, 2026-10-25) its item map `s`'s (each key's lease, the
lessor's `itemMap` and the leases' item sets). -/
def leasesLive (E : AEnv GF) (s : List EtcdKv) : IProp GF :=
  iprop(∃ L : List w64, txn.leasesKnown L s ∗ lease.lessorUser E.γ.leases L (mvcc.leaseItemsOf s) ∗
    ltHalf E L)

/-- **The apply thread's KV resources** at the committed log `log`: the store's reader slots,
the KV's writer of `log` (`txn.kvWriter`: the sole writer, and for a watchable store the writer's
half of its notified log; unit N4), every lease of its state live, the auth store's reader resource
(`E.RD`, 2026-10-14, unit A2), and the sole writer's own resources on the store's backend
(`mvcc.writerOwn`, D22 receiver epochs, S5a: its backend token, which the writes under the batch
lock borrow; until then the reader slots' own). -/
def kvOwn (E : AEnv GF) (log : mvcc.Log) : IProp GF :=
  iprop(mvcc.storeReader E.s E.γ ∗ txn.kvWriter E.s E.γ log ∗
    leasesLive E (mvcc.stateAfter log) ∗ E.RD ∗ mvcc.writerOwn E.γ)

open Iris.ProofMode in
/-- The auth store's reader resource of the apply thread's KV resources, lent out (unit A2). -/
theorem kvOwn_rd (E : AEnv GF) (log : mvcc.Log) :
    kvOwn E log ⊢ E.RD ∗ (E.RD -∗ kvOwn E log) := by
  unfold kvOwn
  iintro ⟨Hsr, Hsw, Hll, Hrd, Hwo⟩
  iframe Hrd
  iintro Hrd
  iframe

/-- (2026-11-01, J8a: the reader resource borrowed per call) **`A` lends the auth store's reader
resource**: the auth layer's `Apply` borrows `E.RD` from its caller's resources `A` for the admin
check (`IsAdminPermitted`) and gives it back; the apply thread's `A` holds it in `kvOwn`
(`rdLend_kvOwn`). Until then the auth layer's mutex held a copy, so each applier made took one. -/
def rdLend (E : AEnv GF) (A : IProp GF) : IProp GF :=
  iprop(□ (A -∗ E.RD ∗ (E.RD -∗ A)))

instance rdLend_persistent (E : AEnv GF) (A : IProp GF) : Persistent (rdLend E A) := by
  unfold rdLend; infer_instance

open Iris.ProofMode in
/-- A lender framed with more resources (the auth layer's `authInfo`, `L hs`). -/
theorem rdLend_frame (E : AEnv GF) (A X : IProp GF) : rdLend E A ⊢ rdLend E iprop(A ∗ X) := by
  unfold rdLend
  iintro #Hl
  imodintro
  iintro ⟨HA, HX⟩
  ihave ⟨Hrd, Hb⟩ := Hl $$ HA
  iframe Hrd
  iintro Hrd
  iframe HX
  iapply Hb; iexact Hrd

open Iris.ProofMode in
/-- The apply thread's resources lend it through their `kvOwn`. -/
theorem rdLend_kvOwn (E : AEnv GF) (X : IProp GF) (log : mvcc.Log) (Y : IProp GF) :
    ⊢ rdLend E iprop(X ∗ kvOwn E log ∗ Y) := by
  unfold rdLend
  iintro !> ⟨HX, Hkv, HY⟩
  ihave ⟨Hrd, Hb⟩ := kvOwn_rd E log $$ Hkv
  iframe Hrd
  iintro Hrd
  iframe HX HY
  iapply Hb; iexact Hrd

open Iris.ProofMode in
/-- The auth store's reader resource and the lease owner's resource (`leasesLive`'s
`lease.lessorUser`, at the item map of the log's state) of the apply thread's KV resources, lent
out (the lease-keys plan: the auth layer's checks read the item map). -/
theorem kvOwn_lend (E : AEnv GF) (log : mvcc.Log) :
    kvOwn E log ⊢ E.RD ∗ ∃ L : List w64,
      lease.lessorUser E.γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
      (E.RD -∗ lease.lessorUser E.γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) -∗
        kvOwn E log) := by
  unfold kvOwn leasesLive
  iintro ⟨Hsr, Hsw, ⟨%L, #Hk, Hu, Hlt⟩, Hrd, Hwo⟩
  iframe Hrd
  iexists L
  iframe Hu
  iintro Hrd Hu
  iframe Hsr Hsw Hrd Hwo
  iexists L
  iframe Hk Hu Hlt

/-- The KV's certificate of its log (persistent; the vertical slice's unit V2: the trivial
floor). -/
theorem kvOwn_cert (E : AEnv GF) (log : mvcc.Log) :
    kvOwn E log ⊢ kvOwn E log ∗ mvcc.idxCert E.γ.idx log := by
  unfold kvOwn
  iintro ⟨Hrd, Hsw, Hll⟩
  ihave ⟨Hsw, #Hc⟩ := txn.kvWriter_cert E.s E.γ log $$ Hsw
  iframe Hrd Hsw Hll Hc

/-- **The thread-owned resources of the chain `c`'s methods** at its value `a`, for the
principal `info`: the outermost auth layer's `authInfo`, holding `info` (owned while the layer's
`Apply` holds its mutex; A3, 2026-10-23: the principal is an index, so that the methods' posts
can state the request's class for it; the index is a phantom below that layer, whose inner
chain's resources are at any principal), and the inner chain's. -/
def chainRes : Chain → GoInterface → go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF
  | .backend, _, _ => iprop(True)
  | .auth _ c, a, info =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p⌝ ∗
        structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ∗
        structFieldRef authApplierV3 go!"authInfo" p ↦ info ∗
        ∃ info' : go_etcd_io.etcd.server.v3.auth.AuthInfo, chainRes c inner info')
  | .quota c, a, info =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p⌝ ∗
        structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ∗ chainRes c inner info)
  | .capped c, a, info =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p⌝ ∗
        structFieldRef applierV3Capped go!"applierV3" p ↦□ inner ∗ chainRes c inner info)
  | .corrupt c, a, info =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p⌝ ∗
        structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner ∗ chainRes c inner info)

/-- The chain's resources at some principal (after a method that may reset the auth layer's
`authInfo`: `UserGet` and `RoleGet` clear it when they reject, `auth.go`). -/
def chainResAny (c : Chain) (a : GoInterface) : IProp GF :=
  iprop(∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo, chainRes c a info)

theorem chainResAny_of (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    chainRes (GF := GF) c a info ⊢ chainResAny c a := by
  iintro H; iunfold chainResAny; iexists info; iexact H

/-! ## The class of a request through the chain (A3 of the auth plan, 2026-10-23) -/

/-- **The class a run of `rq` through `c` with the outcome `oc` establishes** for the principal
`info` in the mode `M` (persistent): each wrapper that rejects says, if it did not reject, what
the rest says; the (outermost) auth layer says that if it did not reject, its checks passed, so
the request's permissions were granted to `info` at recorded states (`reqClass`). -/
def chainClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Chain → IRRModel → Outcome → IProp GF
  | .backend, _, _ => iprop(True)
  | .auth _ _, rq, oc => iprop(∀ _ : oc ≠ .rejected .auth, reqClass M info rq)
  | .quota c, rq, oc => chainClass M info c rq oc
  | .capped c, rq, oc => iprop(∀ _ : oc ≠ .rejected .noSpace, chainClass M info c rq oc)
  | .corrupt c, rq, oc => iprop(∀ _ : oc ≠ .rejected .corrupt, chainClass M info c rq oc)

instance chainClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (c : Chain) (rq : IRRModel) (oc : Outcome) : Persistent (chainClass (GF := GF) M info c rq oc) := by
  induction c with
  | backend => simp only [chainClass]; infer_instance
  | auth on c ih => simp only [chainClass]; infer_instance
  | quota c ih => simp only [chainClass]; exact ih
  | capped c ih => simp only [chainClass]; infer_instance
  | corrupt c ih => simp only [chainClass]; infer_instance

/-- The request's class gives the chain's, whatever the outcome. -/
theorem chainClass_of_reqClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (c : Chain) (rq : IRRModel) (oc : Outcome) :
    reqClass (GF := GF) M info rq ⊢ chainClass M info c rq oc := by
  induction c with
  | backend => simp only [chainClass]; iintro -; itrivial
  | auth on c ih => simp only [chainClass]; iintro #H %_; iexact H
  | quota c ih => simp only [chainClass]; exact ih
  | capped c ih => simp only [chainClass]; iintro #H %_; iapply ih $$ H
  | corrupt c ih => simp only [chainClass]; iintro #H %_; iapply ih $$ H

/-- A request the auth layer's KV methods do not check: the trivial class. -/
theorem chainClass_nonKV (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (c : Chain) (rq : IRRModel) (oc : Outcome) (h : isKVKind (dispatchKind rq) = false) :
    ⊢ chainClass (GF := GF) M info c rq oc := by
  iintro; iapply chainClass_of_reqClass; iapply reqClass_nonKV M info rq h

/-- The auth layer's rejection says nothing. -/
theorem chainClass_auth_rejected (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (on : Bool) (c : Chain) (rq : IRRModel) :
    ⊢ chainClass (GF := GF) M info (.auth on c) rq (.rejected .auth) := by
  simp only [chainClass]; iintro %h; exact absurd rfl h

/-- The auth layer passed: the request's class. -/
theorem chainClass_auth_pass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (on : Bool) (c : Chain) (rq : IRRModel) (oc : Outcome) :
    reqClass (GF := GF) M info rq ⊢ chainClass M info (.auth on c) rq oc := by
  simp only [chainClass]; iintro #H %_; iexact H

theorem chainClass_quota (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (c : Chain) (rq : IRRModel) (oc : Outcome) :
    chainClass (GF := GF) M info c rq oc ⊢ chainClass M info (.quota c) rq oc := by
  simp only [chainClass]; iintro H; iexact H

theorem chainClass_capped (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (c : Chain) (rq : IRRModel) (oc : Outcome) :
    chainClass (GF := GF) M info c rq oc ⊢ chainClass M info (.capped c) rq oc := by
  simp only [chainClass]; iintro #H %_; iexact H

theorem chainClass_capped_rejected (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (c : Chain) (rq : IRRModel) :
    ⊢ chainClass (GF := GF) M info (.capped c) rq (.rejected .noSpace) := by
  simp only [chainClass]; iintro %h; exact absurd rfl h

theorem chainClass_corrupt_rejected (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (c : Chain) (rq : IRRModel) :
    ⊢ chainClass (GF := GF) M info (.corrupt c) rq (.rejected .corrupt) := by
  simp only [chainClass]; iintro %h; exact absurd rfl h

/-- **The outcome passed the auth layer's checks**: applied, or rejected by the backend. -/
def authPassed : Outcome → Prop
  | .rejected k => k = .backend
  | .applied _ _ => True

/-- Through the uber-applier's chain (`alarmChain`), an outcome that passed the auth layer's
checks has the request's class. -/
theorem chainClass_alarm (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (on ns cr : Bool) (rq : IRRModel) (oc : Outcome) (h : authPassed oc) :
    chainClass (GF := GF) M info (alarmChain on ns cr) rq oc ⊢ reqClass M info rq := by
  have h1 : oc ≠ .rejected .auth := by
    intro e; subst e; simp [authPassed] at h
  have h2 : oc ≠ .rejected .noSpace := by
    intro e; subst e; simp [authPassed] at h
  have h3 : oc ≠ .rejected .corrupt := by
    intro e; subst e; simp [authPassed] at h
  unfold alarmChain baseChain
  cases ns <;> cases cr <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> simp only [chainClass]
  · iintro H; ihave H := H $$ %h1; iexact H
  · iintro H; ihave H := H $$ %h3; ihave H := H $$ %h1; iexact H
  · iintro H; ihave H := H $$ %h2; ihave H := H $$ %h1; iexact H
  · iintro H; ihave H := H $$ %h3; ihave H := H $$ %h2; ihave H := H $$ %h1; iexact H

/-! ## The lease class of a request through the chain (the lease-keys plan, 2026-10-31) -/

/-- **The lease class a run of `rq` through `c` with the outcome `oc` establishes** for the
principal `info` in the mode `M`, at the lease owner's item map `I` (persistent): as `chainClass`,
with the auth layer's `reqLeaseClass` (`checkLeasePuts`: the keys of a put's, a transaction's puts'
or a revocation's lease writable by `info`). A conjunct of its own beside `chainClass` (in `kvPost`
and `kvPostF`, not the auth-on track's `kvPostFL`, whose lessor finds no lease:
`notes/lease-keys-plan.md`, Q5). -/
def chainLeaseClass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) : Chain → IRRModel → Outcome → IProp GF
  | .backend, _, _ => iprop(True)
  | .auth _ _, rq, oc => iprop(∀ _ : oc ≠ .rejected .auth, reqLeaseClass M info I rq)
  | .quota c, rq, oc => chainLeaseClass M info I c rq oc
  | .capped c, rq, oc => iprop(∀ _ : oc ≠ .rejected .noSpace, chainLeaseClass M info I c rq oc)
  | .corrupt c, rq, oc => iprop(∀ _ : oc ≠ .rejected .corrupt, chainLeaseClass M info I c rq oc)

instance chainLeaseClass_persistent (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) (oc : Outcome) :
    Persistent (chainLeaseClass (GF := GF) M info I c rq oc) := by
  induction c with
  | backend => simp only [chainLeaseClass]; infer_instance
  | auth on c ih => simp only [chainLeaseClass]; infer_instance
  | quota c ih => simp only [chainLeaseClass]; exact ih
  | capped c ih => simp only [chainLeaseClass]; infer_instance
  | corrupt c ih => simp only [chainLeaseClass]; infer_instance

/-- The request's lease class gives the chain's, whatever the outcome. -/
theorem chainLeaseClass_of_req (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) (oc : Outcome) :
    reqLeaseClass (GF := GF) M info I rq ⊢ chainLeaseClass M info I c rq oc := by
  induction c with
  | backend => simp only [chainLeaseClass]; iintro -; itrivial
  | auth on c ih => simp only [chainLeaseClass]; iintro #H %_; iexact H
  | quota c ih => simp only [chainLeaseClass]; exact ih
  | capped c ih => simp only [chainLeaseClass]; iintro #H %_; iapply ih $$ H
  | corrupt c ih => simp only [chainLeaseClass]; iintro #H %_; iapply ih $$ H

/-- A request with no lease to check has the trivial lease class. -/
theorem chainLeaseClass_noLease (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) (oc : Outcome)
    (h : dispatchKind rq ≠ .put ∧ dispatchKind rq ≠ .txn ∧ dispatchKind rq ≠ .leaseRevoke) :
    ⊢ chainLeaseClass (GF := GF) M info I c rq oc := by
  iintro; iapply chainLeaseClass_of_req
  unfold reqLeaseClass
  split
  · exact absurd ‹_› h.1
  · exact absurd ‹_› h.2.1
  · exact absurd ‹_› h.2.2
  · itrivial

theorem chainLeaseClass_backend {M : auth.AuthMode} {info : go_etcd_io.etcd.server.v3.auth.AuthInfo}
    {I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64} {rq : IRRModel} {oc : Outcome} :
    ⊢ chainLeaseClass (GF := GF) M info I .backend rq oc := by
  simp only [chainLeaseClass]; iintro; itrivial

theorem chainLeaseClass_auth_rejected (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (on : Bool) (c : Chain) (rq : IRRModel) :
    ⊢ chainLeaseClass (GF := GF) M info I (.auth on c) rq (.rejected .auth) := by
  simp only [chainLeaseClass]; iintro %h; exact absurd rfl h

theorem chainLeaseClass_auth_pass (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (on : Bool) (c : Chain) (rq : IRRModel) (oc : Outcome) :
    reqLeaseClass (GF := GF) M info I rq ⊢ chainLeaseClass M info I (.auth on c) rq oc := by
  simp only [chainLeaseClass]; iintro #H %_; iexact H

theorem chainLeaseClass_quota (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) (oc : Outcome) :
    chainLeaseClass (GF := GF) M info I c rq oc ⊢ chainLeaseClass M info I (.quota c) rq oc := by
  simp only [chainLeaseClass]; iintro H; iexact H

theorem chainLeaseClass_capped (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) (oc : Outcome) :
    chainLeaseClass (GF := GF) M info I c rq oc ⊢ chainLeaseClass M info I (.capped c) rq oc := by
  simp only [chainLeaseClass]; iintro #H %_; iexact H

theorem chainLeaseClass_capped_rejected (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) :
    ⊢ chainLeaseClass (GF := GF) M info I (.capped c) rq (.rejected .noSpace) := by
  simp only [chainLeaseClass]; iintro %h; exact absurd rfl h

theorem chainLeaseClass_corrupt (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) (oc : Outcome) :
    chainLeaseClass (GF := GF) M info I c rq oc ⊢ chainLeaseClass M info I (.corrupt c) rq oc := by
  simp only [chainLeaseClass]; iintro #H %_; iexact H

theorem chainLeaseClass_corrupt_rejected (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (c : Chain) (rq : IRRModel) :
    ⊢ chainLeaseClass (GF := GF) M info I (.corrupt c) rq (.rejected .corrupt) := by
  simp only [chainLeaseClass]; iintro %h; exact absurd rfl h

/-- Through the uber-applier's chain, an outcome that passed the auth layer's checks has the
request's lease class. -/
theorem chainLeaseClass_alarm (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (on ns cr : Bool) (rq : IRRModel) (oc : Outcome) (h : authPassed oc) :
    chainLeaseClass (GF := GF) M info I (alarmChain on ns cr) rq oc ⊢ reqLeaseClass M info I rq := by
  have h1 : oc ≠ .rejected .auth := by
    intro e; subst e; simp [authPassed] at h
  have h2 : oc ≠ .rejected .noSpace := by
    intro e; subst e; simp [authPassed] at h
  have h3 : oc ≠ .rejected .corrupt := by
    intro e; subst e; simp [authPassed] at h
  unfold alarmChain baseChain
  cases ns <;> cases cr <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> simp only [chainLeaseClass]
  · iintro H; ihave H := H $$ %h1; iexact H
  · iintro H; ihave H := H $$ %h3; ihave H := H $$ %h1; iexact H
  · iintro H; ihave H := H $$ %h2; ihave H := H $$ %h1; iexact H
  · iintro H; ihave H := H $$ %h3; ihave H := H $$ %h2; ihave H := H $$ %h1; iexact H

/-- **The admin check of `Apply` passed for the request's principal** (persistent): a request
that needs admin permission (`needAdminPermission`) ran its `applyFunc` only after
`IsAdminPermitted(principalOf rq)` answered `nil`, whose verdict this is (A0); stated for a chain
with the auth layer enabled (`c.authOn`; with it disabled the verdict is trivial, `adminVerdict
.off`). -/
def adminPass (M : auth.AuthMode) (c : Chain) (rq : IRRModel) : IProp GF :=
  iprop(∀ _ : c.authOn = true ∧ needAdminPermission rq = true,
    auth.adminVerdict M (some (principalOf rq)) GoInterface.nil)

instance adminPass_persistent (M : auth.AuthMode) (c : Chain) (rq : IRRModel) :
    Persistent (adminPass (GF := GF) M c rq) := by
  unfold adminPass; infer_instance

/-- A chain without an enabled auth layer: the admin pass is trivial. -/
theorem adminPass_off (M : auth.AuthMode) (c : Chain) (rq : IRRModel) (h : c.authOn = false) :
    ⊢ adminPass (GF := GF) M c rq := by
  unfold adminPass; iintro %hh; simp [h] at hh

/-- The admin pass of a wrapper layer is its inner's (the same `authOn`). -/
theorem adminPass_wrap (M : auth.AuthMode) (c c' : Chain) (rq : IRRModel) (h : c'.authOn = c.authOn) :
    adminPass (GF := GF) M c rq ⊢ adminPass M c' rq := by
  unfold adminPass; rw [h]

/-! ## The outcomes, in the heap -/

/-- The error of a rejection `k`: the corrupt applier's `ErrCorrupt`, the capped applier's
`ErrNoSpace`, the auth store's (not nil, one `errors.Is` can take and one of the auth package's
error variables: `authApplyErrIs`, the contract's; the auth plan's E3i, 2026-10-27),
or the backend's (`bk`, by the request). -/
def rejErrIs (bk : GoInterface → IProp GF) : RejectKind → GoInterface → IProp GF
  | .corrupt, err => txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt err
  | .noSpace, err => txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace err
  | .auth, err => iprop(⌜err ≠ GoInterface.nil⌝ ∗ authApplyErrIs err)
  | .backend, err => bk err

/-- The error of an applied request: `nil`, or the quota's `ErrNoSpace` (`ns`). -/
def noSpaceErrIs (ns : Bool) (err : GoInterface) : IProp GF :=
  if ns then txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace err
  else iprop(⌜err = GoInterface.nil⌝)

/-- **A put's answer** for the outcome `oc` at `log` (`txn.Put` at the sole writer): rejected, no
response; applied, the response at the new revision with the previous key-value if `PrevKv`
asked for it. -/
def putOutcomeIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗
      rejErrIs (fun e => iprop(txn.errVarIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound e ∨
        txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound e)) k err)
  | .applied _ ns => iprop(txn.putResponseIs resp (W64 (log.length : Int))
      (if o.base.prevKV then mvcc.findKey o.key (mvcc.stateAfter log) else none) ∗
      noSpaceErrIs ns err)

/-- **A delete's answer** (`txn.DeleteRange` at the sole writer): the number of keys deleted,
the revision (`writeRev`), the deleted key-values if `PrevKv`. The backend's own rejection (the
range read's context error) does not happen at `context.TODO()` (never done: `txn.DeleteRange`'s
`nd`; 2026-10-12, it was `err ≠ nil ∧ PrevKv`). -/
def deleteOutcomeIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗
      rejErrIs (fun _ => iprop(False)) k err)
  | .applied _ ns => iprop(txn.deleteRangeResponseIs resp
      (W64 ((mvcc.writeRev log (txn.delChanges (mvcc.stateAfter log) o) : Nat) : Int))
      (rangeIn (mvcc.stateAfter log) o).length
      (if o.base.prevKV then rangeIn (mvcc.stateAfter log) o else []) ∗
      noSpaceErrIs ns err)

/-- **A range's answer** (`txn.Range` at the sole writer): `rangeResult` at `log`'s last
revision (with the total count) and the compaction revision `crev` the read observed, without the
context error (at `context.TODO()`, never done: `txn.Range`'s `nd`): no error, or `ErrFutureRev`,
or (M2, `notes/m2-plan.md`, S1) `ErrCompacted` below `crev`. -/
def rangeOutcomeIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗ rejErrIs (fun _ => iprop(False)) k err)
  | .applied _ _ => iprop(∃ crev : Int,
      txn.rangeResult resp err log (W64 ((log.length : Int) - 1)) crev o true ∗
      ⌜err = GoInterface.nil ∨ sint.Z (W64 ((log.length : Int) - 1)) < sint.Z o.base.rev ∨
        sint.Z (mvcc.rangeRev (W64 ((log.length : Int) - 1)) o.base.rev) < crev⌝)

/-- **A transaction's answer** (`txn.Txn` at the sole writer): `checkTxn`'s error, or the
response of the server's run `srvRunTxn` at the revision `writeRev` (`skip`: ranges header-only). -/
def txnOutcomeIs (log : mvcc.Log) (t : TxnModel) (skip : Bool) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗ rejErrIs txn.checkErrIs k err)
  | .applied _ ns => iprop(txn.txnResponseIs skip resp
      (W64 (mvcc.writeRev log (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1
        : Int)) t
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
      noSpaceErrIs ns err)

/-- **An applied write's response header, owned** (the field `hf` of the response; not
persistent): its four id fields (`txn.respHdrOwn`: the txn package allocated the header; the gRPC
layer's `header.fill` writes them), at a log of `NewStore`'s two revisions at least and room for
the write (`putOk`/`delOk`: so the response's revision is not `0`). Beside the outcome's
persistent answer (`putOutcomeIs`, ...) in `putAnswerIs`/`deleteAnswerIs` (2026-10-12, the
request path's unit 3a). -/
def appliedHdr (log : mvcc.Log) (hf : Loc) : IProp GF :=
  iprop(txn.respHdrOwn hf ∗ ⌜2 ≤ log.length ∧ log.length + 4 ≤ 2 ^ 63⌝)

/-- **A put's answer, with the response header** (not persistent): `putOutcomeIs`, and, if
applied, the response header's id fields owned (`appliedHdr`). What `Put`'s triple returns. -/
def putAnswerIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => putOutcomeIs log o resp err (.rejected k)
  | .applied l ns => iprop(putOutcomeIs log o resp err (.applied l ns) ∗
      appliedHdr log (structFieldRef etcdserverpb.PutResponse go!"Header" resp))

/-- **A delete's answer, with the response header** (as `putAnswerIs`). -/
def deleteAnswerIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => deleteOutcomeIs log o resp err (.rejected k)
  | .applied l ns => iprop(deleteOutcomeIs log o resp err (.applied l ns) ∗
      appliedHdr log (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp))

/-- **A transaction's answer, with the response header** (as `putAnswerIs`; 2026-10-12, the
request path's unit 3b: `newTxnResp` allocates the header). -/
def txnAnswerIs (log : mvcc.Log) (t : TxnModel) (skip : Bool) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => txnOutcomeIs log t skip resp err (.rejected k)
  | .applied l ns => iprop(txnOutcomeIs log t skip resp err (.applied l ns) ∗
      appliedHdr log (structFieldRef etcdserverpb.TxnResponse go!"Header" resp))

/-- **The lessor's error of a revocation** (the lease-revoke plan, F3): none, or
`ErrLeaseNotFound` (what the gRPC layer maps to its own code, L4). -/
def revokeErrIs (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∨ ∃ e : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e ∗
      ⌜err = GoInterface.ok e⌝)

instance revokeErrIs_persistent (err : GoInterface) : Persistent (revokeErrIs (GF := GF) err) := by
  unfold revokeErrIs; infer_instance

/-- **A revocation's answer** (the lease-revoke plan, R7, F3): rejected, no response and the
layer's error; applied, a response (not nil), the lessor's error (one `errors.Is` can take, and none
or `ErrLeaseNotFound`). (The lease-expiry plan's X6, 2026-11-04: the response's header moved to
`revokeAnswer`, in `revokeResAfter`, as the grant's in `grantAnswer`.) -/
def revokeOutcomeIs (resp : Loc) (err : GoInterface) : Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗ rejErrIs (fun _ => iprop(False)) k err)
  | .applied _ _ => iprop(⌜resp ≠ null⌝ ∗ applyErrIs err ∗ revokeErrIs err)

/-- **A granted lease's response header** at the header field `hf` (the lease-grant stage, 2.6,
2026-11-03): its id fields owned (`txn.respHdrOwn`) and its revision read-only, the last of the
committed log `log`, which is certified (`idxCert`, `certOk`): what `newHeader` gives at the sole
writer (2.11a). Not `appliedHdr` (`+ 4`), which no grant callee gives. -/
def grantHdr (E : AEnv GF) (log : mvcc.Log) (hf : Loc) : IProp GF :=
  iprop(txn.respHdrOwn hf ∗ ∃ (h : Loc) (rv : w64), hf ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗
    mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜sint.Z rv = (log.length : Int) - 1 ∧ 2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝)

/-- **A granted lease's `*pb.LeaseGrantResponse` `r`** (2.6): its `ID` the grant's, its `TTL` and
`Error` read-only (any values), its header `grantHdr` at some certified log; not `null` (amendment
(H), 2026-11-03: the backend answers `&pb.LeaseGrantResponse{}`). -/
def grantRespIs (E : AEnv GF) (r : Loc) (g : LeaseGrantModel) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" r ↦□ g.id ∗
    (∃ t : w64, structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" r ↦□ t) ∗
    (∃ e : GoString, structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" r ↦□ e) ∗
    ∃ log : mvcc.Log, grantHdr E log (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" r))

/-- **A grant's answer** (2.6, the `authnAnsM` pattern beside `dispatchAnswer`, Q2): for a grant
`g`, the response a `*pb.LeaseGrantResponse`; without error, its fields (`grantRespIs`) and the
lease live in the lessor's history from some index (`leaseLiveFrom`; the lease-expiry plan's X2,
2026-11-04: mode-free, until then `leaseGrantedAt`, which needs the monotone mode; `lease.srvInv`'s
law gives it back at `mono`), and its read-only `ttl` field at least the request's TTL (2026-11-05,
the lease-expiry plan's E3/R5: the granted TTL); `True` for a request with no grant. -/
def grantAnswer (E : AEnv GF) (rq : IRRModel) (resp err : GoInterface) : IProp GF :=
  match rq.leaseGrant with
  | some g => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseGrantResponse.ty) #r⌝ ∗
      ((⌜err = GoInterface.nil⌝ ∗ grantRespIs E r g ∗
          ∃ (i : Nat) (l : Loc) (t : w64), lease.leaseLiveFrom E.γ.leases i g.id l ∗
            lease.lsF go!"ttl" l ↦□ t ∗ ⌜sint.Z g.ttl ≤ sint.Z t⌝) ∨
        ⌜err ≠ GoInterface.nil⌝))
  | none => iprop(True)

/-- **A revocation's `*pb.LeaseRevokeResponse` `r`** (the lease-expiry plan's X6, 2026-11-04,
mirroring the grant's `grantRespIs`): not `null`, its header `grantHdr` at some certified log
(`newHeader`'s, after the revocation). -/
def revokeRespIs (E : AEnv GF) (r : Loc) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗
    ∃ log : mvcc.Log, grantHdr E log (structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" r))

/-- **A revocation's answer** (X6, the user's (a): the lease-grant plan's 2.6 mirrored): for a
revocation, the response a `*pb.LeaseRevokeResponse`; without error, its header (`revokeRespIs`);
`True` for a request with no revocation. -/
def revokeAnswer (E : AEnv GF) (rq : IRRModel) (resp err : GoInterface) : IProp GF :=
  match rq.leaseRevoke with
  | some _ => iprop(∃ r : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeResponse.ty) #r⌝ ∗
      ((⌜err = GoInterface.nil⌝ ∗ revokeRespIs E r) ∨ ⌜err ≠ GoInterface.nil⌝))
  | none => iprop(True)

/-- A revocation's answer with an error: nothing but the response's type. -/
theorem revokeAnswer_err (E : AEnv GF) (rq : IRRModel) (resp : Loc) (err : GoInterface)
    (h : err ≠ GoInterface.nil) :
    ⊢ revokeAnswer (GF := GF) E rq
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeResponse.ty) #resp) err := by
  unfold revokeAnswer
  split
  · iintro; iexists resp; isplitr
    · ipureintro; rfl
    iright; ipureintro; exact h
  · iintro; itrivial

/-- The result of `authApplierV3.Apply`'s admin check failing: a fresh `&Result{Err: err}`, the
auth store's error. -/
def rejectResultIs (ar : Loc) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗ ∃ v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result, ar ↦ v ∗
    ⌜v.Err' ≠ GoInterface.nil ∧ v.Resp' = GoInterface.nil⌝ ∗ applyErrIs v.Err')

/-! ## The methods' pre- and postconditions

Each method of the `applierV3` value `a` of the chain `c`, at the sole writer's log `log`. The
KV methods (and the revocation, which deletes through the store) run the request `rq` (the one
`dispatch` passes on: `dispatchKind rq`) and come to an outcome of `chainStep backendStep c`;
the others leave the log as it is. A method that may write the backend takes the
critical-section contract `csContract P f Pre Q Post` and returns `Post` (it wrote in one
critical section of the batch lock, the hook first) or `Pre` (it did not). The methods that
may open a store write transaction (`Put`, `DeleteRange`, `Txn`, `LeaseRevoke`) take a write
token (`mvcc.storeWT E.γ`: the real backend's write-back budget) and spend it (2026-10-13,
unit 6). -/

/-- **The certificates of the logs `rq` may commit** through the chain `c` at `log` (persistent;
2026-10-14, unit T1): the store's caller certifies (`mvcc.certOk`) the log after every outcome of
`chainStep` (the store's `txnEndPre` asks it of a commit). The KV methods take it; a layer that
passes `rq` on passes it on for its inner chain (`certPre_mono`). The etcd server's: the log after
`rq` is the KV model of the committed raft log through `rq`'s entry. -/
def certPre (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) : IProp GF :=
  iprop(□ ∀ oc : Outcome, ⌜chainStep backendStep c rq log oc⌝ -∗ mvcc.certOk E.γ (oc.logAfter log))

instance certPre_persistent (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) :
    Persistent (certPre E c rq log) := by
  unfold certPre; infer_instance

/-- `certPre` with `v3` (`dispatch` runs the KV methods only then), else nothing. -/
def certPreV (v3 : Bool) (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) : IProp GF :=
  if v3 then certPre E c rq log else iprop(True)

instance certPreV_persistent (v3 : Bool) (E : AEnv GF) (c : Chain) (rq : IRRModel)
    (log : mvcc.Log) : Persistent (certPreV v3 E c rq log) := by
  unfold certPreV; split <;> infer_instance

theorem certPreV_true (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) :
    certPreV true E c rq log ⊢ certPre E c rq log := by
  simp only [certPreV, ↓reduceIte]; exact .rfl

open Iris.ProofMode in
theorem certPre_mono (E : AEnv GF) (c c' : Chain) (rq : IRRModel) (log : mvcc.Log)
    (h : ∀ oc, chainStep backendStep c' rq log oc → chainStep backendStep c rq log oc) :
    certPre E c rq log ⊢ certPre E c' rq log := by
  unfold certPre
  iintro #H
  imodintro
  iintro %oc %hs
  iapply H
  ipureintro; exact h oc hs

theorem certPre_auth (E : AEnv GF) (on : Bool) (c : Chain) (rq : IRRModel) (log : mvcc.Log) :
    certPre E (.auth on c) rq log ⊢ certPre E c rq log :=
  certPre_mono E _ c rq log (fun oc h => by simp only [chainStep]; split <;> simp [h])

theorem certPre_quota (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) :
    certPre E (.quota c) rq log ⊢ certPre E c rq log :=
  certPre_mono E _ c rq log (fun oc h => by simp only [chainStep]; exact h)

theorem certPre_capped (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (hk : cappedRejects (dispatchKind rq) = false) :
    certPre E (.capped c) rq log ⊢ certPre E c rq log :=
  certPre_mono E _ c rq log (fun oc h => by
    simp only [chainStep, hk, Bool.false_eq_true, ↓reduceIte]; split <;> simp [h])

open Iris.ProofMode in
open Iris.ProofMode in
/-- The backend's certificate of the log `log'` it commits. -/
theorem certPre_backend_applied (E : AEnv GF) (rq : IRRModel) (log log' : mvcc.Log) (ns : Bool)
    (h : backendStep rq log (.applied log' ns)) :
    certPre E .backend rq log ⊢ mvcc.certOk E.γ log' := by
  unfold certPre
  iintro #H
  ihave Hc := H $$ %(Outcome.applied log' ns) %h
  simp only [Outcome.logAfter]
  iexact Hc

open Iris.ProofMode in
/-- A commit's certificate as the store's `txnEndPre` asks it (`certOkNext`). -/
theorem certOkNext_of_commitLog (γ : mvcc.StoreNames) (log : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.certOk (GF := GF) γ (mvcc.commitLog log pend) ⊢ mvcc.certOkNext γ log pend := by
  unfold mvcc.certOkNext
  by_cases hp : pend = []
  · iintro #H; ileft; ipureintro; exact hp
  · have hc : mvcc.commitLog log pend = log ++ [pend] := by simp [mvcc.commitLog, hp]
    rw [hc]
    iintro #H; iright; iexact H

/-- The common precondition of a writing method (`info`: the principal, A3). -/
def mPre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainRes c a info ∗ mvcc.csContract E.P E.f Pre Q Post)

/-- The common postcondition of a writing method that leaves the log as it is (the chain's
resources at some principal: `UserGet` and `RoleGet` reset the auth layer's `authInfo` when
they reject). -/
def mPost (E : AEnv GF) (c : Chain) (a : GoInterface) (log : mvcc.Log)
    (Pre Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainResAny c a ∗ (Post ∨ Pre))

/-- The precondition of a method that writes only with `shouldApplyV3` (`v3`: the cluster's):
`cPre v3`, the critical-section contract with `v3`, else `Pre` alone. -/
def mPreV (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log)
    (Pre Q Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainRes c a info ∗ cPre v3 E.P E.f Pre Q Post)

/-- Its postcondition: `cPost v3` (`Post ∨ Pre` with `v3`, else `Pre`: no write). -/
def mPostV (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (log : mvcc.Log)
    (Pre Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainRes c a info ∗ cPost v3 Pre Post)

/-- The postcondition of a KV method on `rq`: an outcome of the chain, its answer `R`, the log
it commits, and the request's class for the principal `info` (A3, `chainClass`) and its lease class
at the owner's item map of the state before it (`chainLeaseClass`, the lease-keys plan). -/
def kvPost (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (log : mvcc.Log) (R : Outcome → IProp GF) (Pre Post : IProp GF) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc⌝ ∗ R oc ∗
    kvOwn E (oc.logAfter log) ∗ chainRes c a info ∗ (Post ∨ Pre) ∗ chainClass E.authMode info c rq oc ∗
    chainLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) c rq oc)

/-- **A floor met** (the vertical slice's unit V2): an outcome where the backend ran (`applied`)
ran at a log extending the floor `F` (a certified log the request's client saw: the backend
opens its transaction at the longer of `F` and the sole writer's log, `txn.pinned_floor`). -/
def floorOkO (F log : mvcc.Log) (oc : Outcome) : Prop :=
  ∀ (l : mvcc.Log) (b : Bool), oc = .applied l b → F <+: log

/-- The postcondition of a KV method on `rq` with a floor `F` (unit V2): `kvPost`'s, the outcome
meeting the floor. -/
def kvPostF (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (log F : mvcc.Log) (R : Outcome → IProp GF) (Pre Post : IProp GF) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc ∧ floorOkO F log oc⌝ ∗ R oc ∗
    kvOwn E (oc.logAfter log) ∗ chainRes c a info ∗ (Post ∨ Pre) ∗ chainClass E.authMode info c rq oc ∗
    chainLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) c rq oc)

/-- `Put(r)`'s precondition: `r` is `rq`'s put `o`. -/
def putPre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.put = some o ∧ dispatchKind rq = .put ∧ putOk log⌝ ∗ certPre E c rq log ∗
    txn.putRequestIs r o ∗
    mvcc.storeWT E.γ ∗ mPre E c a info log Pre Q Post)

/-- `DeleteRange(r)`'s precondition. -/
def deletePre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.deleteRange = some o ∧ dispatchKind rq = .deleteRange ∧ delOk log o⌝ ∗
    certPre E c rq log ∗ txn.deleteRangeRequestIs r o ∗ mvcc.storeWT E.γ ∗
    mPre E c a info log Pre Q Post)

/-- `Range(r)`'s precondition (a read: no contract). -/
def rangePre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) : IProp GF :=
  iprop(⌜rq.range = some o ∧ dispatchKind rq = .range ∧ rangeOk log o⌝ ∗
    txn.rangeRequestIs r o ∗ kvOwn E log ∗ chainRes c a info)

/-- `Range(r)`'s postcondition. -/
def rangePost (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc⌝ ∗ rangeOutcomeIs log o resp err oc ∗
    kvOwn E (oc.logAfter log) ∗ chainRes c a info ∗ chainClass E.authMode info c rq oc)

/-- `Txn(r, skip)`'s precondition. -/
def txnPre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (t : TxnModel) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.txn = some t ∧ dispatchKind rq = .txn ∧ txn.TxnPre log t⌝ ∗ certPre E c rq log ∗
    txn.txnRequestIs r t ∗
    mvcc.storeWT E.γ ∗ mPre E c a info log Pre Q Post)

/-- **What a revocation takes beside the method's resources** (the lease-revoke plan, D4): the
range deleter held, the revocable lessor, the rest at `rs`; (the lease-expiry plan's X7, "the revoke
post names the outcome", 2026-11-04) the apply thread's half of the live set at `T` (`ltHalf`, the
other half is `kvOwn`'s `leasesLive`) and the revocable mode. (Until then a cluster that granted
none, `E.lg = false`.) -/
def revokeRes (E : AEnv GF) (T : List w64) (rs : RestM) : IProp GF :=
  iprop(lease.rdAt E.γ.leases E.s ∗ lease.lessorRevocable E.γ.leases ∗ ltHalf E T ∗ E.RO rs ∗
    ⌜E.lm = .revocable⌝)

/-- **What `dispatch` holds for a revocation** (the lease-expiry plan's X7, 2026-11-04): the
lessor's range deleter (`rdAt`, the apply thread's) and its mode revocable, for a request
dispatched as a revocation; nothing otherwise. Taken and given back by `dispatch` and `Apply`. -/
def revokeOwn (E : AEnv GF) (rq : IRRModel) : IProp GF :=
  if dispatchKind rq = .leaseRevoke then
    iprop(lease.rdAt E.γ.leases E.s ∗ lease.lessorRevocable E.γ.leases)
  else iprop(True)

theorem revokeOwn_nonRevoke (E : AEnv GF) (rq : IRRModel) (h : dispatchKind rq ≠ .leaseRevoke) :
    revokeOwn (GF := GF) E rq = iprop(True) := by
  unfold revokeOwn; rw [if_neg h]

/-- **What it gives back, by the outcome `o`** (R6; X7's "names the outcome"): the range deleter,
the revocable lessor, the half at `revokeIds` (the live set without the lease when applied) and the
rest at `revokeRest` (the lease's record deleted when it was live, `id ∈ T`); (X6, 2026-11-04) the
answer of the response `resp` and error `err` (`revokeAnswer`: without error, its header). -/
def revokeResAfter (E : AEnv GF) (rq : IRRModel) (T : List w64) (rs : RestM) (resp : Loc)
    (err : GoInterface) (o : Outcome) : IProp GF :=
  iprop(lease.rdAt E.γ.leases E.s ∗ lease.lessorRevocable E.γ.leases ∗
    ltHalf E (revokeIds rq true o T) ∗ E.RO (revokeRest T rq true o rs) ∗
    revokeAnswer E rq
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeResponse.ty) #resp) err)

/-- `LeaseRevoke(r)`'s precondition (the lease-revoke plan, R3, 2026-10-31): the request's, room
for a revision (`putOk`: `rqOk` keeps excluding the kind for `dispatch`), the certificate, the
write token, the method's resources and the revocation's (`revokeRes`). -/
def revokePre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (id : w64) (log : mvcc.Log) (T : List w64) (rs : RestM)
    (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.leaseRevoke = some id ∧ dispatchKind rq = .leaseRevoke ∧ putOk log⌝ ∗
    certPre E c rq log ∗
    leaseRevokeIs r id ∗
    mvcc.storeWT E.γ ∗ mPre E c a info log Pre Q Post ∗ revokeRes E T rs)

/-! ### The backend's posts: no chain resources, the trivial class -/

theorem chainClass_backend {M : auth.AuthMode} {info : go_etcd_io.etcd.server.v3.auth.AuthInfo}
    {rq : IRRModel} {oc : Outcome} : ⊢ chainClass (GF := GF) M info .backend rq oc := by
  simp only [chainClass]; iintro; itrivial

theorem chainResAny_backend {a : GoInterface} : ⊢ chainResAny (GF := GF) .backend a := by
  iintro; iunfold chainResAny; iexists zeroValDef; simp only [chainRes]; itrivial

theorem kvPostF_backend {E : AEnv GF} {a : GoInterface} {info : go_etcd_io.etcd.server.v3.auth.AuthInfo}
    {rq : IRRModel} {log F : mvcc.Log} {R : Outcome → IProp GF} {Pre Post : IProp GF} :
    (∃ oc : Outcome, ⌜chainStep backendStep .backend rq log oc ∧ floorOkO F log oc⌝ ∗ R oc ∗
      kvOwn E (oc.logAfter log) ∗ chainRes .backend a info ∗ (Post ∨ Pre)) ⊢
      kvPostF E .backend a info rq log F R Pre Post := by
  iintro ⟨%oc, %H, HR, Hkv, Hres, HPP⟩
  unfold kvPostF
  iexists oc
  iframe HR Hkv Hres HPP
  isplitr
  · ipureintro; exact H
  isplitl
  · iapply chainClass_backend
  · iapply chainLeaseClass_backend

theorem rangePost_backend {E : AEnv GF} {a : GoInterface} {info : go_etcd_io.etcd.server.v3.auth.AuthInfo}
    {rq : IRRModel} {o : OpFull} {log : mvcc.Log} {resp : Loc} {err : GoInterface} :
    (∃ oc : Outcome, ⌜chainStep backendStep .backend rq log oc⌝ ∗ rangeOutcomeIs log o resp err oc ∗
      kvOwn E (oc.logAfter log) ∗ chainRes .backend a info) ⊢
      rangePost E .backend a info rq o log resp err := by
  iintro ⟨%oc, %H, HR, Hkv, Hres⟩
  unfold rangePost
  iexists oc
  iframe HR Hkv Hres
  isplitr
  · ipureintro; exact H
  iapply chainClass_backend

theorem mPost_backend {E : AEnv GF} {a : GoInterface} {log : mvcc.Log} {Pre Post : IProp GF} :
    kvOwn E log ∗ (Post ∨ Pre) ⊢ mPost E .backend a log Pre Post := by
  iintro ⟨Hkv, HPP⟩
  unfold mPost
  iframe Hkv HPP
  iapply chainResAny_backend

/-- The request facts of a one-argument method that leaves the log as it is, by method: what
the layers read of the request (`R r`); `True` for those passed on unread to the auth store. The
auth store's requests are admitted in the environment's mode only (`adminAdmitted`, the auth plan's
E2i). -/
def reqFacts (E : AEnv GF) (m : GoString) (r : Loc) : IProp GF :=
  if m = go!"LeaseCheckpoint" then
    iprop((∃ cms : List CheckpointModel, leaseCheckpointIs r cms ∗ ⌜cms.length ≤ 1⌝) ∗ E.RW)
  else if m = go!"Alarm" then iprop((∃ am : AlarmModel, alarmRequestIs r am) ∗ E.RW)
  else if m = go!"Authenticate" then
    iprop(((∃ am : AuthenticateModel, authenticateIs r am) ∗ E.RW) ∗ ⌜adminAdmitted E.authMode⌝)
  else if m = go!"UserGet" then
    iprop(((∃ n : GoString, authUserGetIs r n) ∗ E.RW) ∗ ⌜adminAdmitted E.authMode⌝)
  else if m = go!"UserAdd" then
    iprop(((∃ m : UserAddModel, authUserAddIs r m ∗ ⌜m.name.length ≤ backend.maxKeySize⌝) ∗ E.RW) ∗
      ⌜adminAdmitted E.authMode⌝)
  else if m = go!"RoleAdd" then
    iprop(((∃ n : GoString, authRoleAddIs r n ∗ ⌜n.length ≤ backend.maxKeySize⌝) ∗ E.RW) ∗
      ⌜adminAdmitted E.authMode⌝)
  else if m = go!"RoleGet" then
    iprop(((∃ n : GoString, authRoleGetIs r n) ∗ E.RW) ∗ ⌜adminAdmitted E.authMode⌝)
  else iprop(E.RW ∗ ⌜adminAdmitted E.authMode⌝)

/-- **A cluster method's request facts** (D22, 2026-10-23): the request `r` of the method `m`
(`ClusterReq.method`) holds `cr`; `DowngradeInfoSet`'s with the write right `E.RW`. (The
cluster-rows stage, 2026-11-02: of the rest state `rs` the applier contract's cluster row binds,
`ClusterVersionSet`'s version not above the server's, `ClusterMemberAttrSet`'s member a member of
`rs.mem`: the specs' premises; `dispatch` takes them from `rqOk` and `restReqOk`.) -/
def clusterFacts (E : AEnv GF) (m : GoString) (cr : ClusterReq) (r : Loc) (rs : RestM) : IProp GF :=
  match cr with
  | .ver v => iprop(⌜m = go!"ClusterVersionSet"⌝ ∗ clusterVersionSetIs r v ∗
      ⌜semverValid v ∧ semverAtMostServer v⌝)
  | .attr a => iprop(⌜m = go!"ClusterMemberAttrSet"⌝ ∗ memberAttrSetIs r a ∗
      ⌜(rs.mem.lookup a.memberID).isSome = true⌝)
  | .dg d => iprop(⌜m = go!"DowngradeInfoSet"⌝ ∗ downgradeInfoSetIs r d ∗ E.RW)

/-- The methods `(resp, err) = m(r)` that leave the log as it is (the lease checkpoint, the
alarm, and the auth store's requests; the grant has its own triple since the lease-grant stage,
2.11): writers the workload does not reach,
their facts with the write right `E.RW` (`reqFacts`, D22, 2026-10-23). -/
def respMethods : List GoString :=
  [go!"LeaseCheckpoint", go!"Alarm", go!"Authenticate", go!"UserAdd",
    go!"UserDelete", go!"UserChangePassword", go!"UserGrantRole", go!"UserGet",
    go!"UserRevokeRole", go!"RoleAdd", go!"RoleGrantPermission", go!"RoleGet",
    go!"RoleRevokePermission", go!"RoleDelete", go!"UserList", go!"RoleList"]

/-- The methods `m(r, shouldApplyV3)` returning nothing (the cluster's). -/
def clusterMethods : List GoString :=
  [go!"ClusterVersionSet", go!"ClusterMemberAttrSet", go!"DowngradeInfoSet"]

/-- The methods `(resp, err) = m()` that may write (enabling or disabling auth). -/
def resp0Methods : List GoString := [go!"AuthEnable", go!"AuthDisable"]

/-! ## The triples of an applier value -/

/-- **A trace a KV method returns** (unit P1b, 2026-10-14): `nil`, or owned (`ownTrace`).
`dispatch` stores it in the result (`resTrace`), which the apply thread hands, through the wait,
to the goroutine serving the request (`raftRequest` steps and logs it). -/
def traceRes (t : Loc) : IProp GF :=
  iprop(⌜t = null⌝ ∨ ∃ e : Bool, traceutil.ownTrace t e)

theorem traceRes_null : ⊢ traceRes (GF := GF) null := by
  unfold traceRes; iintro; ileft; ipureintro; rfl


/-- **The consistent index's resources, lent out of `Pre`** (D14i, 2026-10-17): the critical
section's precondition `Pre` holds a resource `C` that `ConsistentIndex` reads under
(`E.ciC C x`, at the value `x` it reads), which a method may take out and put back before it
locks. -/
def ciSplit (E : AEnv GF) (Pre : IProp GF) : IProp GF :=
  iprop(□ (Pre -∗ ∃ (C : IProp GF) (x : w64), ⌜E.ciC C x⌝ ∗ C ∗ (C -∗ Pre)))

instance ciSplit_persistent (E : AEnv GF) (Pre : IProp GF) : Persistent (ciSplit E Pre) := by
  unfold ciSplit; infer_instance

/-- **`ciSplit` at a known index** (C1's A2, 2026-10-28): the resource `C` lent out of `Pre` is
one under which `ConsistentIndex` reads `x`. -/
def ciSplitAt (E : AEnv GF) (Pre : IProp GF) (x : w64) : IProp GF :=
  iprop(□ (Pre -∗ ∃ C : IProp GF, ⌜E.ciC C x⌝ ∗ C ∗ (C -∗ Pre)))

instance ciSplitAt_persistent (E : AEnv GF) (Pre : IProp GF) (x : w64) :
    Persistent (ciSplitAt E Pre x) := by
  unfold ciSplitAt; infer_instance

theorem ciSplit_of_at (E : AEnv GF) (Pre : IProp GF) (x : w64) :
    ciSplitAt (GF := GF) E Pre x ⊢ ciSplit E Pre := by
  iintro #H
  iunfold ciSplit
  iintro !> HP
  iunfold ciSplitAt at H
  ihave ⟨%C, %h, HC, Hb⟩ := H $$ HP
  iexists C, x
  iframe HC Hb
  ipureintro; exact h

/-! ## The compaction arm (M2, the apply side, 2026-10-31) -/

/-! ## The apply thread's compaction resources -/

/-- **The store's compaction right at `c`, by the mode**: a compacting store's restorable right
(`mvcc.compactRightR`: half the compaction revision's authority, the jobs' queue, the closer's and
the jobs' shares of the fields), at least `-1`; a store that does not compact, none, at `-1`. -/
def cmpRight (E : AEnv GF) (c : Int) : IProp GF :=
  if mvcc.kbCmpM E.γ.kb then iprop(mvcc.compactRightR E.s E.γ c ∗ ⌜-1 ≤ c⌝) else iprop(⌜c = -1⌝)

/-- **The apply thread's compaction resources at `c`**: the right by the mode and the compaction's
write-back supply (persistent; `True` off). -/
def cmpOwn (E : AEnv GF) (c : Int) : IProp GF :=
  iprop(cmpRight E c ∗ mvcc.kbWTSupplyM E.γ.kb)

theorem cmpOwn_off (E : AEnv GF) (c : Int) (h : ¬ mvcc.kbCmpM E.γ.kb) :
    cmpOwn (GF := GF) E c ⊢ ⌜c = -1⌝ := by
  unfold cmpOwn cmpRight
  simp only [h, ↓reduceIte]
  iintro ⟨%hc, -⟩
  ipureintro; exact hc

/-- **At a store that does not compact, the resources are free at `-1`** (`cmpRight`'s off arm,
`kbWTSupplyM`'s `True`): what a producer of the apply thread's state over such a store gives
(the boot, the state after a snapshot's install). -/
theorem cmpOwn_of_off (E : AEnv GF) (h : ¬ mvcc.kbCmpM E.γ.kb) : ⊢ cmpOwn (GF := GF) E (-1) := by
  unfold cmpOwn cmpRight mvcc.kbWTSupplyM
  simp only [h, ↓reduceIte]
  iintro
  isplitr
  · ipureintro; trivial
  itrivial

theorem cmpOwn_ge (E : AEnv GF) (c : Int) : cmpOwn (GF := GF) E c ⊢ ⌜-1 ≤ c⌝ := by
  unfold cmpOwn cmpRight
  split
  · iintro ⟨⟨-, %h⟩, -⟩; ipureintro; exact h
  · iintro ⟨%h, -⟩; ipureintro; omega



/-- **A successful compaction's response** `rp` (owned: `EtcdServer.Compact` writes it): its
header, owned (`Compaction`'s last lines, `rr.Rev` of `KV.Range(context.TODO(), "compaction", …)`).
(2026-10-31, the switch: the draft's header revision `|log| - 1` dropped: no caller reads it,
`compactResultIs` only owns the header, and `readView.Range` takes no lower bound of the log it
reads, so the revision is that of some certified log, not provably the apply thread's.) -/
def cmpRespOk (rp : Loc) : IProp GF :=
  iprop(⌜rp ≠ null⌝ ∗ ∃ cv : etcdserverpb.CompactionResponse, rp ↦ cv ∗
    ∃ hv : etcdserverpb.ResponseHeader, cv.Header' ↦ hv)

/-- **The answer of the chain `c`'s `Compaction(rev)`** at the compaction revision
`crev`: through a chain that reaches the backend, a response at the current revision with its trace
(`rev` above `crev`), or `ErrCompacted` with no response and no trace (`rev` at or below `crev`); the
corrupt applier's `ErrCorrupt`. The channel (`Physc`) is not stated: the request path reads it only
of a physical compaction, which the proposers never send (`compactReqIs`). -/
def cmpAnswerIs (c : Chain) (crev : Int) (rev : w64) (resp : Loc) (ch : GoChan)
    (trace : Loc) (err : GoInterface) : IProp GF :=
  if chainCompacts c then
    iprop((⌜crev < sint.Z rev ∧ err = GoInterface.nil⌝ ∗ cmpRespOk resp ∗ traceRes trace) ∨
      (⌜sint.Z rev ≤ crev ∧ resp = null ∧ trace = null ∧ err ≠ GoInterface.nil⌝ ∗
        txn.errVarIs go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted err))
  else
    iprop(⌜resp = null ∧ ch = chan.nil ∧ trace = null⌝ ∗
      txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt err)

/-- **The chain `c`'s `Compaction` triple** (M2, the apply side, item 9; `applierTriples`' last
conjunct): `Compaction(cr)` for the request's `*pb.CompactionRequest` `cr` at the
revision `rev` (`compactionIs`), admitted (`cmpAdmit`'s facts at `rev`), with the apply thread's KV
at `log` and the critical-section contract (`mPre`: `store.Compact`'s `SetScheduledCompact` writes
under the batch lock), and its compaction resources at `crev`: the KV and the chain's resources as
they were, the contract's `Post` or `Pre`, the compaction resources at the revision after it
(`cmpRevAfter crev rev` through a chain that reaches the backend), the answer (`cmpAnswerIs`).
Its proof for the backend rests on `store.Compact.spec` (F-1: no `ErrFutureRev` arm, which
`cmpAnswerIs` has no case for). -/
def cmpTriple (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ (cr : Loc) (rev : w64) (log : mvcc.Log) (crev : Int) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ compactionIs cr rev ∗ ⌜cmpAdmitRev E.γ.kb log rev⌝ ∗ mvcc.crevPermAt E.γ (sint.Z rev) ∗
          mPre E c (.ok ai) info log Pre Q Post ∗ cmpOwn E crev }}
        (App (Val #(methods ai.ty go!"Compaction" ai.v)) (Val #cr))
      {{ (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface),
          RET (PairV (PairV (PairV #resp #ch) #trace) #err);
          kvOwn E log ∗ chainRes c (.ok ai) info ∗ (Post ∨ Pre) ∗
          cmpOwn E (if chainCompacts c then cmpRevAfter crev rev else crev) ∗
          cmpAnswerIs c crev rev resp ch trace err }}))

/-- **A request's compactions are permitted** (C3's server stage, 2026-11-02; persistent): its
revision is one the store's compaction permit holds of (`mvcc.crevPermAt`, what `store.Compact`
takes), beside the pure facts `cmpAdmit`, as they gated by the kind. Free of a request of another
kind. -/
def cmpPermRq (E : AEnv GF) (rq : IRRModel) : IProp GF :=
  iprop(□ (⌜dispatchKind rq = .compaction⌝ → ∀ r : w64, ⌜rq.compaction = some r⌝ →
    mvcc.crevPermAt E.γ (sint.Z r)))

instance cmpPermRq_persistent (E : AEnv GF) (rq : IRRModel) :
    Persistent (cmpPermRq (GF := GF) E rq) := by
  unfold cmpPermRq; infer_instance

theorem cmpPermRq_nonCmp (E : AEnv GF) (rq : IRRModel) (h : dispatchKind rq ≠ .compaction) :
    ⊢ cmpPermRq (GF := GF) E rq := by
  iunfold cmpPermRq
  iintro !> %hk
  exact absurd hk h

/-- **A grant's permits** (the lease-grant plan's 2.10, S2; the `cmpPermRq` pattern): for a request
dispatched as a grant, its id is one the lessor may grant (`leaseGranted`). Free of a request of
another kind. (The lease-expiry plan's X2, 2026-11-04: until then also the lessor monotone,
`lessorModeIs … true`.) -/
def grantPermRq (E : AEnv GF) (rq : IRRModel) : IProp GF :=
  iprop(□ (⌜dispatchKind rq = .leaseGrant⌝ → ∀ g : LeaseGrantModel, ⌜rq.leaseGrant = some g⌝ →
    lease.leaseGranted E.γ.leases g.id))

instance grantPermRq_persistent (E : AEnv GF) (rq : IRRModel) :
    Persistent (grantPermRq (GF := GF) E rq) := by
  unfold grantPermRq; infer_instance

theorem grantPermRq_of_not_grant (E : AEnv GF) (rq : IRRModel)
    (h : dispatchKind rq ≠ .leaseGrant) : ⊢ grantPermRq (GF := GF) E rq := by
  iunfold grantPermRq
  iintro !> %hk
  exact absurd hk h

/-- A wrapper that passes `Compaction` on answers as its inner chain. -/
theorem cmpAnswerIs_congr (c c' : Chain) (h : chainCompacts c = chainCompacts c') (crev : Int)
    (rev : w64) (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface) :
    cmpAnswerIs (GF := GF) c crev rev resp ch trace err = cmpAnswerIs c' crev rev resp ch trace err := by
  unfold cmpAnswerIs; rw [h]

instance cmpTriple_persistent (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) :
    Persistent (cmpTriple E c ai) := by
  unfold cmpTriple; infer_instance

/-- **The grant triple's precondition** (2.11): in a cluster that grants leases (`E.lg`, which
`dispatch` has from `rqOk E.lg`'s grant arm: without it the two halves are `True` and do not tie the
lessor's live set to `T`), a request dispatched as the grant `g` (its request `r`), the lease marked granted (`grantPermRq`'s; the lease-expiry plan's X2: no longer the lessor's mode), the
apply thread's half of the live set `T`, the rest resource at `rs`, the store's write token, the
common precondition and the consistent index's split; (the lease-expiry plan's E3 (c), 2026-11-05)
the apply thread's half of the ids the lessor ever had, `U` (`lease.leaseEver`), and the grant's id
new to them unless the lessor is monotone (`lease.lessor.Grant.spec`'s premise). -/
def grantPre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (g : LeaseGrantModel) (log : mvcc.Log) (T : List w64) (rs : RestM)
    (U : List w64) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜E.lg = true ∧ rq.leaseGrant = some g ∧ dispatchKind rq = .leaseGrant⌝ ∗ leaseGrantIs r g ∗
    lease.leaseGranted E.γ.leases g.id ∗ ltHalf E T ∗
    E.RO rs ∗ mvcc.storeWT E.γ ∗ mPre E c a info log Pre Q Post ∗ ciSplit E Pre ∗
    lease.leaseEver E.γ.leases U ∗ (lease.lessorModeIs E.γ.leases true ∨ ⌜g.id ∉ U⌝))

/-- **The grant triple's postcondition** (2.11) at the outcome `o`: the chain's step
(`chainStep backendStep`), applied exactly without error, which is exactly when the chain lets the
grant through and the lessor's condition holds at `T`; the half of the live set and the rest
resource after it (`grantIds`, `grantRest`, the record's TTL `t` the lessor's), the ids the lessor
ever had after it (`grantIds` of `U`: the grant's id added exactly when applied), the answer. -/
def grantPost (E : AEnv GF) (c : Chain) (a : GoInterface) (rq : IRRModel) (g : LeaseGrantModel)
    (log : mvcc.Log) (T : List w64) (rs : RestM) (U : List w64) (Pre Post : IProp GF) (resp : Loc)
    (err : GoInterface) (o : Outcome) : IProp GF :=
  iprop(mPost E c a log Pre Post ∗ applyErrIs err ∗
    -- (amendment (E), 2026-11-03) the backend's rejection is the lessor's error
    (⌜o = .rejected .backend⌝ -∗ lease.lessorErrIs err) ∗
    ⌜chainStep backendStep c rq log o ∧ ((∃ l ns, o = .applied l ns) ↔ err = GoInterface.nil) ∧
      (err = GoInterface.nil ↔ grantGoes c rq = true ∧ grantIdsOk T g.id g.ttl)⌝ ∗
    ltHalf E (grantIds rq true o T) ∗ (∃ t : w64, E.RO (grantRest t rq true o rs)) ∗
    lease.leaseEver E.γ.leases (grantIds rq true o U) ∗
    grantAnswer E rq (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseGrantResponse.ty) #resp) err)

/-- **The method triples of the `applierV3` value `ai` of the chain `c`** in the environment
`E` (each persistent: `dispatch` calls one per request). Each takes the principal `info` the
chain's resources hold (A3, 2026-10-23); `Apply` hands its `applyFunc` the resources at the
request's principal (`principalOf rq`), takes them back at any, and says its admin check passed
for it (`adminPass`); `Compaction` (`cmpTriple`, M2's apply side, 2026-10-31). -/
def applierTriples (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) : IProp GF :=
  iprop(
    -- the KV methods
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log F : mvcc.Log) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ putPre E c (.ok ai) info r rq o log Pre Q Post ∗ mvcc.idxCert E.γ.idx F }}
        (App (Val #(methods ai.ty go!"Put" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPostF E c (.ok ai) info rq log F (putAnswerIs log o resp err) Pre Post ∗ traceRes trace }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log F : mvcc.Log) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ deletePre E c (.ok ai) info r rq o log Pre Q Post ∗ mvcc.idxCert E.γ.idx F }}
        (App (Val #(methods ai.ty go!"DeleteRange" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPostF E c (.ok ai) info rq log F (deleteAnswerIs log o resp err) Pre Post ∗ traceRes trace }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ rangePre E c (.ok ai) info r rq o log }}
        (App (Val #(methods ai.ty go!"Range" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          rangePost E c (.ok ai) info rq o log resp err ∗ traceRes trace }}) ∗
    □ (∀ (r : Loc) (skip : Bool) (rq : IRRModel) (t : TxnModel) (log F : mvcc.Log)
        (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ txnPre E c (.ok ai) info r rq t log Pre Q Post ∗ mvcc.idxCert E.γ.idx F }}
        (App (App (Val #(methods ai.ty go!"Txn" ai.v)) (Val #r)) (Val #skip))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPostF E c (.ok ai) info rq log F (txnAnswerIs log t skip resp err) Pre Post ∗ traceRes trace }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (id : w64) (log : mvcc.Log) (T : List w64) (rs : RestM)
        (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ revokePre E c (.ok ai) info r rq id log T rs Pre Q Post }}
        (App (Val #(methods ai.ty go!"LeaseRevoke" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvPost E c (.ok ai) info rq log
            (fun o => iprop(revokeOutcomeIs resp err o ∗ revokeResAfter E rq T rs resp err o)) Pre Post }}) ∗
    -- (the lease-grant stage, 2.11) `LeaseGrant`
    □ (∀ (r : Loc) (rq : IRRModel) (g : LeaseGrantModel) (log : mvcc.Log) (T : List w64)
        (rs : RestM) (U : List w64) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ grantPre E c (.ok ai) info r rq g log T rs U Pre Q Post }}
        (App (Val #(methods ai.ty go!"LeaseGrant" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          ∃ o : Outcome, grantPost E c (.ok ai) rq g log T rs U Pre Post resp err o }}) ∗
    -- the methods that leave the log as it is
    □ (∀ (m : GoString) (r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo), ⌜m ∈ respMethods⌝ -∗
      {{ reqFacts E m r ∗ mPre E c (.ok ai) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗ ciSplit E Pre }}
        (App (Val #(methods ai.ty m ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          mPost E c (.ok ai) log Pre Post ∗ applyErrIs err }}) ∗
    □ (∀ (m : GoString) (log : mvcc.Log) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo), ⌜m ∈ resp0Methods⌝ -∗
      ⌜(m = go!"AuthEnable" → E.authOn = true) ∧ adminAdmitted E.authMode⌝ -∗
      {{ mPre E c (.ok ai) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗ E.RW }}
        (App (Val #(methods ai.ty m ai.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          mPost E c (.ok ai) log Pre Post ∗ applyErrIs err }}) ∗
    □ (∀ (log : mvcc.Log) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ kvOwn E log ∗ chainRes c (.ok ai) info }}
        (App (Val #(methods ai.ty go!"AuthStatus" ai.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvOwn E log ∗ chainRes c (.ok ai) info ∗ applyErrIs err }}) ∗
    □ (∀ (m : GoString) (r : Loc) (v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF)
        (cr : ClusterReq) (rs : RestM) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      ⌜m ∈ clusterMethods⌝ -∗
      {{ clusterFacts E m cr r rs ∗ mPreV v3 E c (.ok ai) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗ E.FS ∗
          E.RO rs }}
        (App (App (Val #(methods ai.ty m ai.v)) (Val #r)) (Val #v3))
      {{ RET #(); mPostV v3 E c (.ok ai) info log Pre Post ∗ E.FS ∗ E.RO (cr.eff v3 rs) }}) ∗
    -- `Apply`: the `applyFunc` under the chain's resources at the request's principal, or the
    -- auth layers' admin rejection
    □ (∀ (r : Loc) (rq : IRRModel) (skip v3 : Bool) (af : GoFunc) (A : IProp GF)
        (B : Loc → IProp GF),
      {{ irrWrapperIs r rq skip ∗ A ∗ rdLend E A ∗
          ({{ chainRes c (.ok ai) (principalOf rq) ∗ A }} (App (App (Val #af) (Val #r)) (Val #v3))
            {{ (ar : Loc), RET #ar; chainResAny c (.ok ai) ∗ B ar }}) }}
        (App (App (App (Val #(methods ai.ty go!"Apply" ai.v)) (Val #r)) (Val #v3)) (Val #af))
      {{ (ar : Loc), RET #ar;
          (B ar ∗ adminPass E.authMode c rq) ∨
            (⌜needAdminPermission rq = true⌝ ∗ A ∗ rejectResultIs ar) }}) ∗
    -- (M2, the apply side, item 9) `Compaction`
    cmpTriple E c ai)

instance applierTriples_persistent (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) :
    Persistent (applierTriples E c ai) := by
  unfold applierTriples; infer_instance

/-- **The `applierV3` value `a` of the chain `c`** in the environment `E`: an interface value
whose methods satisfy `applierTriples`. -/
def applierSpec (E : AEnv GF) (c : Chain) (a : GoInterface) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗ applierTriples E c ai)

instance applierSpec_persistent (E : AEnv GF) (c : Chain) (a : GoInterface) :
    Persistent (applierSpec E c a) := by
  unfold applierSpec; infer_instance

/-! ## The layers' structs -/

/-- **The backend's options** `opts` in the environment `E`: a logger, the KV (the store `E.s`,
whose hook is `E.f` under `E.P`), and the components with their contracts. -/
def backendOptsOk (E : AEnv GF) (opts : ApplierOptions) : IProp GF :=
  iprop(⌜opts.Logger' ≠ null⌝ ∗ isApplyKV opts.KV' E.s E.γ ∗ mvcc.hookOk E.γ E.P E.f ∗
    isApplyLessor opts.Lessor' E.s E.γ E.P E.f E.RO E.RW ∗
    isAuthStore opts.AuthStore' E.γ E.P E.f E.RD E.authMode E.RW ∗
    isAlarmStore opts.AlarmStore' E.γ E.P E.f E.RW ∗ isCluster opts.Cluster' E.γ E.P E.f E.RO E.RW ∗
    isRaftStatus opts.RaftStatus' ∗ isSnapshotServer opts.SnapshotServer' E.FS ∗
    isConsistentIndexer opts.ConsistentIndex' E.ciC)

instance backendOptsOk_persistent (E : AEnv GF) (opts : ApplierOptions) :
    Persistent (backendOptsOk E opts) := by
  unfold backendOptsOk; infer_instance

/-- **The `*applierV3backend` `p`**: its options, read-only. -/
def backendIs (E : AEnv GF) (p : Loc) : IProp GF :=
  iprop(∃ opts : ApplierOptions, structFieldRef applierV3backend go!"options" p ↦□ opts ∗
    backendOptsOk E opts)

instance backendIs_persistent (E : AEnv GF) (p : Loc) : Persistent (backendIs E p) := by
  unfold backendIs; infer_instance

/-- **The `*quotaApplierV3` `p`**: its inner applier and its quota, read-only. -/
def quotaIs (p : Loc) (inner : GoInterface) : IProp GF :=
  iprop(structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ∗ ∃ q : GoInterface,
    structFieldRef quotaApplierV3 go!"q" p ↦□ q ∗ isQuota q)

instance quotaIs_persistent (p : Loc) (inner : GoInterface) :
    Persistent (quotaIs (GF := GF) p inner) := by
  unfold quotaIs; infer_instance

/-- **The `*applierV3Capped` `p`**: its inner applier, read-only (its `q`, a zero
`BackendQuota`, is only `Cost`'s receiver). -/
def cappedIs (p : Loc) (inner : GoInterface) : IProp GF :=
  iprop(structFieldRef applierV3Capped go!"applierV3" p ↦□ inner)

instance cappedIs_persistent (p : Loc) (inner : GoInterface) :
    Persistent (cappedIs (GF := GF) p inner) := by
  unfold cappedIs; infer_instance

/-- **The `*applierV3Corrupt` `p`**: its inner applier, read-only. -/
def corruptIs (p : Loc) (inner : GoInterface) : IProp GF :=
  iprop(structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner)

instance corruptIs_persistent (p : Loc) (inner : GoInterface) :
    Persistent (corruptIs (GF := GF) p inner) := by
  unfold corruptIs; infer_instance

/-- The auth layer's mutex's resource: its `authInfo`, the zero `AuthInfo` between `Apply`s
(set at construction, `newAuthApplierV3`; reset after every `Apply`, and by `UserGet` and
`RoleGet` when they reject, `auth.go`). -/
def authInfoIdle (p : Loc) : IProp GF :=
  iprop(structFieldRef authApplierV3 go!"authInfo" p ↦
    (zeroValDef : go_etcd_io.etcd.server.v3.auth.AuthInfo))

/-- **The `*authApplierV3` `p`**: its inner applier, auth store and lessor, read-only, with
their contracts, and its mutex, whose resource is its `authInfo` (2026-11-01, J8a: until then also a
reader resource of the auth store, `E.RD`, unit A2, which `Apply` now borrows from its caller,
`rdLend`). -/
def authIs (E : AEnv GF) (p : Loc) (inner : GoInterface) : IProp GF :=
  iprop(structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ∗
    (∃ st : GoInterface, structFieldRef authApplierV3 go!"as" p ↦□ st ∗
      isAuthStore st E.γ E.P E.f E.RD E.authMode E.RW) ∗
    (∃ le : GoInterface, structFieldRef authApplierV3 go!"lessor" p ↦□ le ∗
      isApplyLessor le E.s E.γ E.P E.f E.RO E.RW) ∗
    sync.isMutex (structFieldRef authApplierV3 go!"mu" p) (authInfoIdle p))

instance authIs_persistent (E : AEnv GF) (p : Loc) (inner : GoInterface) :
    Persistent (authIs E p inner) := by
  unfold authIs; infer_instance

/-- **The shape of `newApplierV3`'s applier** `a` (the auth plan's E2m, 2026-10-26): an auth
applier over a quota applier over a backend applier with the options `opts`, their fields
read-only (what `applierAdmin`'s layers, `AdminChain.lean`, need of the chain's values). -/
def baseShape (opts : ApplierOptions) (a : GoInterface) : IProp GF :=
  iprop(∃ pa pq pb : Loc, ⌜a = interface.mkOk (go.GoType.PointerType authApplierV3.ty) #pa⌝ ∗
    structFieldRef authApplierV3 go!"applierV3" pa ↦□
      (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #pq : GoInterface) ∗
    structFieldRef quotaApplierV3 go!"applierV3" pq ↦□
      (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #pb : GoInterface) ∗
    structFieldRef applierV3backend go!"options" pb ↦□ opts)

instance baseShape_persistent (opts : ApplierOptions) (a : GoInterface) :
    Persistent (baseShape (GF := GF) opts a) := by
  unfold baseShape; infer_instance

/-- **The shape of `restoreAlarms`' applier** `a` over the base applier `base` (the auth plan's
E2o, 2026-10-26): `newApplierV3Capped` of `base` if a `NOSPACE` alarm is set (`ns`), then
`newApplierV3Corrupt` of that if a `CORRUPT` alarm is (`cr`), their fields read-only (what
`applierAdmin_alarm`, `AdminChain.lean`, needs to lift the base's admin triples). -/
def cappedShape : Bool → GoInterface → GoInterface → IProp GF
  | true, base, a => iprop(∃ pc : Loc,
      ⌜a = interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #pc⌝ ∗ cappedIs pc base)
  | false, base, a => iprop(⌜a = base⌝)

/-- The corrupt wrapper's part of `alarmShape`. -/
def corruptShape : Bool → GoInterface → GoInterface → IProp GF
  | true, inner, a => iprop(∃ pr : Loc,
      ⌜a = interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #pr⌝ ∗ corruptIs pr inner)
  | false, inner, a => iprop(⌜a = inner⌝)

def alarmShape (ns cr : Bool) (base a : GoInterface) : IProp GF :=
  iprop(∃ a1 : GoInterface, cappedShape ns base a1 ∗ corruptShape cr a1 a)

instance alarmShape_persistent (ns cr : Bool) (base a : GoInterface) :
    Persistent (alarmShape (GF := GF) ns cr base a) := by
  unfold alarmShape
  cases ns <;> cases cr <;> simp only [cappedShape, corruptShape, cappedIs, corruptIs] <;> infer_instance

end defs

end apply
end EtcdGrove
end Perennial
