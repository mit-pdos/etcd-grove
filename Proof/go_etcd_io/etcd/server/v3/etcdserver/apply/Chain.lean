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
      dispatchKind rq ≠ .txn)

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
component's error). Compaction is out of the model (`False`), and so is a request with no field
set (`dispatch` panics). 2026-10-15 (unit T2): the put's, the delete's and the transaction's cases
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
  | .leaseRevoke => ∃ pend : List mvcc.Change, (∀ ch ∈ pend, ch.isDel = true) ∧
      o = .applied (mvcc.commitLog log pend) false
  | .compaction => False
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

/-- **The per-request premise** of `rq` at the sole writer's log `log`, by what `dispatch` does
with it: the txn package's for a KV request (`TxnPre` for a transaction); a lease checkpoint
request with at most one checkpoint (each checkpoint is its own critical section of the batch
lock: `issues/etcd-apply-lease-checkpoint-sections.md`; until 2026-10-17); a cluster version that
parses. **No lease request** (D14h, 2026-10-17, the user's decision): the workload has no
`LeaseGrant`, `LeaseRevoke` or `LeaseCheckpoint` (with no lease granted none expires, so the
lessor proposes no revocation and no checkpoint); `lessor.Revoke` is not specified (unit T3).
**No alarm, auth or downgrade request** (D22, 2026-10-23: the backend over every bucket): their
writers take the environment's write right `AEnv.RW` (the server's is `False`: the apply thread
holds the rest buckets at their model, `RestModel.lean`), so `dispatch` does not call them; no
workload admits one (the server's `plainCover`). Until then their premise was `True` (the user's
and role's name within the key bound for `UserAdd`/`RoleAdd`). -/
def rqOk (log : mvcc.Log) (rq : IRRModel) : Prop :=
  match dispatchKind rq with
  | .put => putOk log
  | .deleteRange => ∀ o, rq.deleteRange = some o → delOk log o
  | .range => ∀ o, rq.range = some o → rangeOk log o
  | .txn => ∀ t, rq.txn = some t → txn.TxnPre log t
  | .leaseGrant => False
  | .leaseRevoke => False
  | .leaseCheckpoint => False
  | .clusterVersionSet => ∀ v, rq.clusterVersionSet = some v → semverValid v
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

/-- **The admin requests admitted in the mode `on`** (the auth plan's E2m, continued): their shape
only, the names within bbolt's key bound (the step specs' premise; the fuel bounds the rest,
`AuthFuel.lean`). `SetUp`'s `UserAdd`, `RoleAdd`, `AuthEnable`; not yet `UserGrantRole` and
`RoleGrantPermission`, whose user's and role's names the request model does not record (`IRRModel`
keeps only their presence), nor the other admin kinds. -/
def adminKindOk (rq : IRRModel) : Prop :=
  match dispatchKind rq with
  | .authUserAdd => ∀ n, rq.authUserAdd = some n → n.length ≤ backend.maxKeySize
  | .authRoleAdd => ∀ n, rq.authRoleAdd = some n → n.length ≤ backend.maxKeySize
  | .authEnable => True
  | _ => False

/-- **The per-request premise in the auth mode `M`** (E2m, continued): `rqOk`, or, in the mode `on`
only, an admitted admin request (`adminKindOk`). A second clause rather than a mode-indexed
`rqOk`: `rqOk` and every statement written with it (the entries' claims, the examples' workloads)
keep their text, and in the mode `off` the two agree (`rqOkM_off`). -/
def rqOkM (M : auth.AuthMode) (log : mvcc.Log) (rq : IRRModel) : Prop :=
  rqOk log rq ∨ (M.isOn = true ∧ adminKindOk rq)

theorem rqOkM_off (log : mvcc.Log) (rq : IRRModel) : rqOkM .off log rq ↔ rqOk log rq := by
  simp [rqOkM, auth.AuthMode.isOn]

theorem rqOkM_of_rqOk (M : auth.AuthMode) (log : mvcc.Log) (rq : IRRModel) (h : rqOk log rq) :
    rqOkM M log rq := Or.inl h

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  precondition (`ciSplit`) -/
  ciC : IProp GF → Prop
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

/-- Whether the auth store may refuse (`Chain.auth E.authOn`; until the auth plan's A0 a field):
`false` exactly in the mode `off`. -/
def AEnv.authOn (E : AEnv GF) : Bool := E.authMode.isOn

theorem AEnv.authOn_eq (E : AEnv GF) : E.authOn = E.authMode.isOn := rfl

/-- **The live leases of the state `s`** (2026-10-13, unit 8 of the backend): the lease owner's
resource at some live set `L` (its half of the lessor's live set, a reader slot of its lock) of
which every lease of `s` is. -/
def leasesLive (γ : mvcc.StoreNames) (s : List EtcdKv) : IProp GF :=
  iprop(∃ L : List w64, txn.leasesKnown L s ∗ lease.lessorUser γ.leases L)

/-- **The apply thread's KV resources** at the committed log `log`: the store's reader slots,
the KV's writer of `log` (`txn.kvWriter`: the sole writer, and for a watchable store the writer's
half of its notified log; unit N4), every lease of its state live, the auth store's reader resource
(`E.RD`, 2026-10-14, unit A2), and the sole writer's own resources on the store's backend
(`mvcc.writerOwn`, D22 receiver epochs, S5a: its backend token, which the writes under the batch
lock borrow; until then the reader slots' own). -/
def kvOwn (E : AEnv GF) (log : mvcc.Log) : IProp GF :=
  iprop(mvcc.storeReader E.s E.γ ∗ txn.kvWriter E.s E.γ log ∗
    leasesLive E.γ (mvcc.stateAfter log) ∗ E.RD ∗ mvcc.writerOwn E.γ)

open Iris.ProofMode in
/-- The auth store's reader resource of the apply thread's KV resources, lent out (unit A2). -/
theorem kvOwn_rd (E : AEnv GF) (log : mvcc.Log) :
    kvOwn E log ⊢ E.RD ∗ (E.RD -∗ kvOwn E log) := by
  unfold kvOwn
  iintro ⟨Hsr, Hsw, Hll, Hrd, Hwo⟩
  iframe Hrd
  iintro Hrd
  iframe

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
`ErrNoSpace`, the auth store's (not nil, one `errors.Is` can take: `applyErrIs`, the contract's),
or the backend's (`bk`, by the request). -/
def rejErrIs (bk : GoInterface → IProp GF) : RejectKind → GoInterface → IProp GF
  | .corrupt, err => txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCorrupt err
  | .noSpace, err => txn.errVarIs go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace err
  | .auth, err => iprop(⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)
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
revision (with the total count), without the context error (at `context.TODO()`, never done:
`txn.Range`'s `nd`): no error, or `ErrFutureRev`. -/
def rangeOutcomeIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗ rejErrIs (fun _ => iprop(False)) k err)
  | .applied _ _ => iprop(txn.rangeResult resp err log (W64 ((log.length : Int) - 1)) o true ∗
      ⌜err = GoInterface.nil ∨ sint.Z (W64 ((log.length : Int) - 1)) < sint.Z o.base.rev⌝)

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

/-- **A revocation's answer**: rejected, no response; applied, the lessor's error (one
`errors.Is` can take, the contract's). -/
def revokeOutcomeIs (resp : Loc) (err : GoInterface) : Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗ rejErrIs (fun _ => iprop(False)) k err)
  | .applied _ _ => applyErrIs err

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
it commits, and the request's class for the principal `info` (A3, `chainClass`). -/
def kvPost (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (log : mvcc.Log) (R : Outcome → IProp GF) (Pre Post : IProp GF) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc⌝ ∗ R oc ∗
    kvOwn E (oc.logAfter log) ∗ chainRes c a info ∗ (Post ∨ Pre) ∗ chainClass E.authMode info c rq oc)

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
    kvOwn E (oc.logAfter log) ∗ chainRes c a info ∗ (Post ∨ Pre) ∗ chainClass E.authMode info c rq oc)

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

/-- `LeaseRevoke(r)`'s precondition. -/
def revokePre (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (id : w64) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.leaseRevoke = some id ∧ dispatchKind rq = .leaseRevoke ∧ rqOk log rq⌝ ∗
    certPre E c rq log ∗
    leaseRevokeIs r id ∗
    mvcc.storeWT E.γ ∗ mPre E c a info log Pre Q Post)

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
  iapply chainClass_backend

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
  if m = go!"LeaseGrant" then
    iprop((∃ g : LeaseGrantModel, leaseGrantIs r g ∗ lease.leaseGranted E.γ.leases g.id) ∗ E.RW)
  else if m = go!"LeaseCheckpoint" then
    iprop((∃ cms : List CheckpointModel, leaseCheckpointIs r cms ∗ ⌜cms.length ≤ 1⌝) ∗ E.RW)
  else if m = go!"Alarm" then iprop((∃ am : AlarmModel, alarmRequestIs r am) ∗ E.RW)
  else if m = go!"Authenticate" then
    iprop(((∃ am : AuthenticateModel, authenticateIs r am) ∗ E.RW) ∗ ⌜adminAdmitted E.authMode⌝)
  else if m = go!"UserGet" then
    iprop(((∃ n : GoString, authUserGetIs r n) ∗ E.RW) ∗ ⌜adminAdmitted E.authMode⌝)
  else if m = go!"UserAdd" then
    iprop(((∃ n : GoString, authUserAddIs r n ∗ ⌜n.length ≤ backend.maxKeySize⌝) ∗ E.RW) ∗
      ⌜adminAdmitted E.authMode⌝)
  else if m = go!"RoleAdd" then
    iprop(((∃ n : GoString, authRoleAddIs r n ∗ ⌜n.length ≤ backend.maxKeySize⌝) ∗ E.RW) ∗
      ⌜adminAdmitted E.authMode⌝)
  else if m = go!"RoleGet" then
    iprop(((∃ n : GoString, authRoleGetIs r n) ∗ E.RW) ∗ ⌜adminAdmitted E.authMode⌝)
  else iprop(E.RW ∗ ⌜adminAdmitted E.authMode⌝)

/-- **A cluster method's request facts** (D22, 2026-10-23): the request `r` of the method `m`
(`ClusterReq.method`) holds `cr`; `DowngradeInfoSet`'s with the write right `E.RW`. -/
def clusterFacts (E : AEnv GF) (m : GoString) (cr : ClusterReq) (r : Loc) : IProp GF :=
  match cr with
  | .ver v => iprop(⌜m = go!"ClusterVersionSet"⌝ ∗ clusterVersionSetIs r v ∗ ⌜semverValid v⌝)
  | .attr a => iprop(⌜m = go!"ClusterMemberAttrSet"⌝ ∗ memberAttrSetIs r a)
  | .dg d => iprop(⌜m = go!"DowngradeInfoSet"⌝ ∗ downgradeInfoSetIs r d ∗ E.RW)

/-- The methods `(resp, err) = m(r)` that leave the log as it is (the lease grant and
checkpoint, the alarm, and the auth store's requests): writers the workload does not reach,
their facts with the write right `E.RW` (`reqFacts`, D22, 2026-10-23). -/
def respMethods : List GoString :=
  [go!"LeaseGrant", go!"LeaseCheckpoint", go!"Alarm", go!"Authenticate", go!"UserAdd",
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
(`E.ciC C`), which a method may take out and put back before it locks. -/
def ciSplit (E : AEnv GF) (Pre : IProp GF) : IProp GF :=
  iprop(□ (Pre -∗ ∃ C : IProp GF, ⌜E.ciC C⌝ ∗ C ∗ (C -∗ Pre)))

instance ciSplit_persistent (E : AEnv GF) (Pre : IProp GF) : Persistent (ciSplit E Pre) := by
  unfold ciSplit; infer_instance

/-- **The method triples of the `applierV3` value `ai` of the chain `c`** in the environment
`E` (each persistent: `dispatch` calls one per request). Each takes the principal `info` the
chain's resources hold (A3, 2026-10-23); `Apply` hands its `applyFunc` the resources at the
request's principal (`principalOf rq`), takes them back at any, and says its admin check passed
for it (`adminPass`). -/
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
    □ (∀ (r : Loc) (rq : IRRModel) (id : w64) (log : mvcc.Log) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ revokePre E c (.ok ai) info r rq id log Pre Q Post }}
        (App (Val #(methods ai.ty go!"LeaseRevoke" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvPost E c (.ok ai) info rq log (revokeOutcomeIs resp err) Pre Post }}) ∗
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
      {{ clusterFacts E m cr r ∗ mPreV v3 E c (.ok ai) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗ E.FS ∗
          E.RO rs }}
        (App (App (Val #(methods ai.ty m ai.v)) (Val #r)) (Val #v3))
      {{ RET #(); mPostV v3 E c (.ok ai) info log Pre Post ∗ E.FS ∗ E.RO (cr.eff v3 rs) }}) ∗
    -- `Apply`: the `applyFunc` under the chain's resources at the request's principal, or the
    -- auth layers' admin rejection
    □ (∀ (r : Loc) (rq : IRRModel) (skip v3 : Bool) (af : GoFunc) (A : IProp GF)
        (B : Loc → IProp GF),
      {{ irrWrapperIs r rq skip ∗ A ∗
          ({{ chainRes c (.ok ai) (principalOf rq) ∗ A }} (App (App (Val #af) (Val #r)) (Val #v3))
            {{ (ar : Loc), RET #ar; chainResAny c (.ok ai) ∗ B ar }}) }}
        (App (App (App (Val #(methods ai.ty go!"Apply" ai.v)) (Val #r)) (Val #v3)) (Val #af))
      {{ (ar : Loc), RET #ar;
          (B ar ∗ adminPass E.authMode c rq) ∨
            (⌜needAdminPermission rq = true⌝ ∗ A ∗ rejectResultIs ar) }}))

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
    isApplyLessor opts.Lessor' E.s E.γ E.P E.f E.RW ∗
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

/-- **The `*applierV3Corrupt` `p`**: its inner applier, read-only. -/
def corruptIs (p : Loc) (inner : GoInterface) : IProp GF :=
  iprop(structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner)

/-- The auth layer's mutex's resource: its `authInfo`, the zero `AuthInfo` between `Apply`s
(set at construction, `newAuthApplierV3`; reset after every `Apply`, and by `UserGet` and
`RoleGet` when they reject, `auth.go`). -/
def authInfoIdle (p : Loc) : IProp GF :=
  iprop(structFieldRef authApplierV3 go!"authInfo" p ↦
    (zeroValDef : go_etcd_io.etcd.server.v3.auth.AuthInfo))

/-- **The `*authApplierV3` `p`**: its inner applier, auth store and lessor, read-only, with
their contracts, and its mutex, whose resource is its `authInfo` and a reader resource of the auth
store (`E.RD`: `Apply`'s admin check; 2026-10-14, unit A2). -/
def authIs (E : AEnv GF) (p : Loc) (inner : GoInterface) : IProp GF :=
  iprop(structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ∗
    (∃ st : GoInterface, structFieldRef authApplierV3 go!"as" p ↦□ st ∗
      isAuthStore st E.γ E.P E.f E.RD E.authMode E.RW) ∗
    (∃ le : GoInterface, structFieldRef authApplierV3 go!"lessor" p ↦□ le ∗
      isApplyLessor le E.s E.γ E.P E.f E.RW) ∗
    sync.isMutex (structFieldRef authApplierV3 go!"mu" p) iprop(authInfoIdle p ∗ E.RD))

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

end defs

end apply
end EtcdGrove
end Perennial
