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
outcome commits (`Outcome.logAfter`).

**An applier value** (`applierSpec E c a`): the triples of the `applierV3` interface value `a`'s
methods, as the chain `c` runs them (persistent; every method but `Compaction`, which is out of
the model). The thread-owned resources a chain's methods need (`chainRes c a`): the auth layer's
`authInfo` (its `Apply` takes them from its mutex and hands them to the `applyFunc`, which hands
them to the methods; the other layers own nothing). Each layer's methods are `Spec/`+`Proof/`
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel

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
  | auth (c : Chain)
  | quota (c : Chain)
  | capped (c : Chain)
  | corrupt (c : Chain)
  deriving DecidableEq

/-- `newApplierV3`'s chain: `authApplierV3` over `quotaApplierV3` over `applierV3backend`. -/
def baseChain : Chain := .auth (.quota .backend)

/-- `restoreAlarms`' chain: the base chain, `capped` if a `NOSPACE` alarm is set, then `corrupt`
if a `CORRUPT` alarm is. -/
def alarmChain (noSpace corrupt : Bool) : Chain :=
  let c := if noSpace then Chain.capped baseChain else baseChain
  if corrupt then .corrupt c else c

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
  | .auth c, rq, log, o =>
      if authChecks (dispatchKind rq) ∨ needAdminPermission rq = true then
        o = .rejected .auth ∨ chainStep B c rq log o
      else chainStep B c rq log o
  | .quota c, rq, log, o =>
      if quotaChecks (dispatchKind rq) then
        ∃ o', chainStep B c rq log o' ∧
          (o = o' ∨ ∃ log', o' = .applied log' false ∧ o = .applied log' true)
      else chainStep B c rq log o

/-! ## The backend's relation -/

/-- **What the backend applier does with `rq` at the sole writer's log `log`** (the txn package's
results, `backend.go`): a put is the txn package's `Put` (the lease not found or, with an ignore
flag, the key missing: rejected; else the one change `putChangeOf` committed); a delete the
filter (`delChanges` committed; or, with `PrevKv`, the range read's error); a range reads `log`;
a transaction is `checkTxn`'s error or the server's run `srvRunTxn` committed (nothing for a
read-only one); a revocation commits the lessor's deletions of the lease's keys; the other
requests do not touch the KV (applied, or the component's error). Compaction is out of the model
(`False`), and so is a request with no field set (`dispatch` panics). -/
def backendStep (rq : IRRModel) (log : mvcc.Log) (o : Outcome) : Prop :=
  match dispatchKind rq with
  | .put => ∃ op, rq.put = some op ∧
      ((op.leaseID ≠ W64 0 ∧ o = .rejected .backend) ∨
       (txn.needsPrev op = true ∧ mvcc.findKey op.key (mvcc.stateAfter log) = none ∧
         o = .rejected .backend) ∨
       o = .applied (log ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter log))]])
         false)
  | .deleteRange => ∃ op, rq.deleteRange = some op ∧
      (o = .applied (mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) op)) false ∨
       (op.base.prevKV = true ∧ o = .rejected .backend))
  | .range => o = .applied log false
  | .txn => ∃ t, rq.txn = some t ∧
      (o = .rejected .backend ∨
       (o = .applied (mvcc.commitLog log
           (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1) false ∧
        (txn.txnReadonly t = true →
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 = [])))
  | .leaseRevoke => ∃ pend : List mvcc.Change, (∀ ch ∈ pend, ch.isDel = true) ∧
      o = .applied (mvcc.commitLog log pend) false
  | .compaction => False
  | .none => False
  | _ => o = .applied log false ∨ o = .rejected .backend

/-! ## The per-request premises -/

/-- A put's premise at the sole writer's log: room for one more revision. -/
def putOk (log : mvcc.Log) : Prop := log.length + 4 ≤ 2 ^ 63

/-- A delete's premises: room for one more revision, fewer than `2 ^ 63` keys. -/
def delOk (log : mvcc.Log) : Prop :=
  log.length + 4 ≤ 2 ^ 63 ∧ (mvcc.stateAfter log).length < 2 ^ 63

/-- A range's premises: room for the read, a valid sort target, the sort's premise. -/
def rangeOk (log : mvcc.Log) (o : OpFull) : Prop :=
  log.length + 3 ≤ 2 ^ 63 ∧ txn.validSortTarget o ∧ txn.sortOk o log

/-- **The per-request premise** of `rq` at the sole writer's log `log`, by what `dispatch` does
with it: the txn package's for a KV request (`TxnPre` for a transaction); a lease checkpoint
request with at most one checkpoint (each checkpoint is its own critical section of the batch
lock: `issues/etcd-apply-lease-checkpoint-sections.md`); a cluster version that parses. -/
def rqOk (log : mvcc.Log) (rq : IRRModel) : Prop :=
  match dispatchKind rq with
  | .put => putOk log
  | .deleteRange => delOk log
  | .range => ∀ o, rq.range = some o → rangeOk log o
  | .txn => ∀ t, rq.txn = some t → txn.TxnPre log t
  | .leaseCheckpoint => ∀ cs, rq.leaseCheckpoint = some cs → cs.length ≤ 1
  | .clusterVersionSet => ∀ v, rq.clusterVersionSet = some v → semverValid v
  | _ => True

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The environment and the thread's resources -/

/-- **A chain's environment**: the store `s` (ghost names `γ`) the backend's KV is, and its
backend's batch lock's invariant `P` and post-lock hook `f`. -/
structure AEnv (GF : BundledGFunctors) where
  s : Loc
  γ : mvcc.StoreNames
  P : IProp GF
  f : val

/-- **The apply thread's KV resources** at the committed log `log`: the store's reader slots,
the sole writer of `log`, every lease of its state known. -/
def kvOwn (E : AEnv GF) (log : mvcc.Log) : IProp GF :=
  iprop(mvcc.storeReader E.s E.γ ∗ txn.soleWriter E.γ log ∗
    txn.leasesKnown E.γ.leases (mvcc.stateAfter log))

/-- **The thread-owned resources of the chain `c`'s methods** at its value `a`: the auth layers'
`authInfo` (owned while the layer's `Apply` holds its mutex), and the inner chain's. -/
def chainRes : Chain → GoInterface → IProp GF
  | .backend, _ => iprop(True)
  | .auth c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p⌝ ∗
        structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ∗
        (∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo,
          structFieldRef authApplierV3 go!"authInfo" p ↦ info) ∗
        chainRes c inner)
  | .quota c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p⌝ ∗
        structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ∗ chainRes c inner)
  | .capped c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p⌝ ∗
        structFieldRef applierV3Capped go!"applierV3" p ↦□ inner ∗ chainRes c inner)
  | .corrupt c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p⌝ ∗
        structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner ∗ chainRes c inner)

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
critical section of the batch lock, the hook first) or `Pre` (it did not). -/

/-- The common precondition of a writing method. -/
def mPre (E : AEnv GF) (c : Chain) (a : GoInterface) (log : mvcc.Log)
    (Pre Q Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainRes c a ∗ mvcc.csContract E.P E.f Pre Q Post)

/-- The common postcondition of a writing method that leaves the log as it is. -/
def mPost (E : AEnv GF) (c : Chain) (a : GoInterface) (log : mvcc.Log)
    (Pre Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainRes c a ∗ (Post ∨ Pre))

/-- The precondition of a method that writes only with `shouldApplyV3` (`v3`: the cluster's):
`cPre v3`, the critical-section contract with `v3`, else `Pre` alone. -/
def mPreV (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface) (log : mvcc.Log)
    (Pre Q Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainRes c a ∗ cPre v3 E.P E.f Pre Q Post)

/-- Its postcondition: `cPost v3` (`Post ∨ Pre` with `v3`, else `Pre`: no write). -/
def mPostV (v3 : Bool) (E : AEnv GF) (c : Chain) (a : GoInterface) (log : mvcc.Log)
    (Pre Post : IProp GF) : IProp GF :=
  iprop(kvOwn E log ∗ chainRes c a ∗ cPost v3 Pre Post)

/-- The postcondition of a KV method on `rq`: an outcome of the chain, its answer `R`, the log
it commits. -/
def kvPost (E : AEnv GF) (c : Chain) (a : GoInterface) (rq : IRRModel) (log : mvcc.Log)
    (R : Outcome → IProp GF) (Pre Post : IProp GF) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc⌝ ∗ R oc ∗
    kvOwn E (oc.logAfter log) ∗ chainRes c a ∗ (Post ∨ Pre))

/-- `Put(r)`'s precondition: `r` is `rq`'s put `o`. -/
def putPre (E : AEnv GF) (c : Chain) (a : GoInterface) (r : Loc) (rq : IRRModel) (o : OpFull)
    (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.put = some o ∧ dispatchKind rq = .put ∧ putOk log⌝ ∗ txn.putRequestIs r o ∗
    mPre E c a log Pre Q Post)

/-- `DeleteRange(r)`'s precondition. -/
def deletePre (E : AEnv GF) (c : Chain) (a : GoInterface) (r : Loc) (rq : IRRModel)
    (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.deleteRange = some o ∧ dispatchKind rq = .deleteRange ∧ delOk log⌝ ∗
    txn.deleteRangeRequestIs r o ∗ mPre E c a log Pre Q Post)

/-- `Range(r)`'s precondition (a read: no contract). -/
def rangePre (E : AEnv GF) (c : Chain) (a : GoInterface) (r : Loc) (rq : IRRModel)
    (o : OpFull) (log : mvcc.Log) : IProp GF :=
  iprop(⌜rq.range = some o ∧ dispatchKind rq = .range ∧ rangeOk log o⌝ ∗
    txn.rangeRequestIs r o ∗ kvOwn E log ∗ chainRes c a)

/-- `Range(r)`'s postcondition. -/
def rangePost (E : AEnv GF) (c : Chain) (a : GoInterface) (rq : IRRModel) (o : OpFull)
    (log : mvcc.Log) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc⌝ ∗ rangeOutcomeIs log o resp err oc ∗
    kvOwn E (oc.logAfter log) ∗ chainRes c a)

/-- `Txn(r, skip)`'s precondition. -/
def txnPre (E : AEnv GF) (c : Chain) (a : GoInterface) (r : Loc) (rq : IRRModel)
    (t : TxnModel) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.txn = some t ∧ dispatchKind rq = .txn ∧ txn.TxnPre log t⌝ ∗ txn.txnRequestIs r t ∗
    mPre E c a log Pre Q Post)

/-- `LeaseRevoke(r)`'s precondition. -/
def revokePre (E : AEnv GF) (c : Chain) (a : GoInterface) (r : Loc) (rq : IRRModel)
    (id : w64) (log : mvcc.Log) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.leaseRevoke = some id ∧ dispatchKind rq = .leaseRevoke⌝ ∗ leaseRevokeIs r id ∗
    mPre E c a log Pre Q Post)

/-- The request facts of a one-argument method that leaves the log as it is, by method: what
the layers read of the request (`R r`); `True` for those passed on unread to the auth store. -/
def reqFacts (m : GoString) (r : Loc) : IProp GF :=
  if m = go!"LeaseGrant" then iprop(∃ g : LeaseGrantModel, leaseGrantIs r g)
  else if m = go!"LeaseCheckpoint" then
    iprop(∃ cms : List CheckpointModel, leaseCheckpointIs r cms ∗ ⌜cms.length ≤ 1⌝)
  else if m = go!"Alarm" then iprop(∃ am : AlarmModel, alarmRequestIs r am)
  else if m = go!"Authenticate" then iprop(∃ am : AuthenticateModel, authenticateIs r am)
  else if m = go!"UserGet" then iprop(∃ n : GoString, authUserGetIs r n)
  else if m = go!"RoleGet" then iprop(∃ n : GoString, authRoleGetIs r n)
  else if m = go!"ClusterVersionSet" then
    iprop(∃ v : GoString, clusterVersionSetIs r v ∗ ⌜semverValid v⌝)
  else if m = go!"ClusterMemberAttrSet" then iprop(∃ mm : MemberAttrModel, memberAttrSetIs r mm)
  else if m = go!"DowngradeInfoSet" then iprop(∃ dm : DowngradeModel, downgradeInfoSetIs r dm)
  else iprop(True)

/-- The methods `(resp, err) = m(r)` that leave the log as it is (the lease grant and
checkpoint, the alarm, and the auth store's requests). -/
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

/-- **The method triples of the `applierV3` value `ai` of the chain `c`** in the environment
`E` (each persistent: `dispatch` calls one per request). -/
def applierTriples (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) : IProp GF :=
  iprop(
    -- the KV methods
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF),
      {{ putPre E c (.ok ai) r rq o log Pre Q Post }}
        (App (Val #(methods ai.ty go!"Put" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPost E c (.ok ai) rq log (putAnswerIs log o resp err) Pre Post }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF),
      {{ deletePre E c (.ok ai) r rq o log Pre Q Post }}
        (App (Val #(methods ai.ty go!"DeleteRange" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPost E c (.ok ai) rq log (deleteAnswerIs log o resp err) Pre Post }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log),
      {{ rangePre E c (.ok ai) r rq o log }}
        (App (Val #(methods ai.ty go!"Range" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          rangePost E c (.ok ai) rq o log resp err }}) ∗
    □ (∀ (r : Loc) (skip : Bool) (rq : IRRModel) (t : TxnModel) (log : mvcc.Log)
        (Pre Q Post : IProp GF),
      {{ txnPre E c (.ok ai) r rq t log Pre Q Post }}
        (App (App (Val #(methods ai.ty go!"Txn" ai.v)) (Val #r)) (Val #skip))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPost E c (.ok ai) rq log (txnAnswerIs log t skip resp err) Pre Post }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (id : w64) (log : mvcc.Log) (Pre Q Post : IProp GF),
      {{ revokePre E c (.ok ai) r rq id log Pre Q Post }}
        (App (Val #(methods ai.ty go!"LeaseRevoke" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvPost E c (.ok ai) rq log (revokeOutcomeIs resp err) Pre Post }}) ∗
    -- the methods that leave the log as it is
    □ (∀ (m : GoString) (r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF), ⌜m ∈ respMethods⌝ -∗
      {{ reqFacts m r ∗ mPre E c (.ok ai) log Pre Q Post }}
        (App (Val #(methods ai.ty m ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          mPost E c (.ok ai) log Pre Post ∗ applyErrIs err }}) ∗
    □ (∀ (m : GoString) (log : mvcc.Log) (Pre Q Post : IProp GF), ⌜m ∈ resp0Methods⌝ -∗
      {{ mPre E c (.ok ai) log Pre Q Post }}
        (App (Val #(methods ai.ty m ai.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          mPost E c (.ok ai) log Pre Post ∗ applyErrIs err }}) ∗
    □ (∀ (log : mvcc.Log),
      {{ kvOwn E log ∗ chainRes c (.ok ai) }}
        (App (Val #(methods ai.ty go!"AuthStatus" ai.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvOwn E log ∗ chainRes c (.ok ai) ∗ applyErrIs err }}) ∗
    □ (∀ (m : GoString) (r : Loc) (v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF),
      ⌜m ∈ clusterMethods⌝ -∗
      {{ reqFacts m r ∗ mPreV v3 E c (.ok ai) log Pre Q Post }}
        (App (App (Val #(methods ai.ty m ai.v)) (Val #r)) (Val #v3))
      {{ RET #(); mPostV v3 E c (.ok ai) log Pre Post }}) ∗
    -- `Apply`: the `applyFunc` under the chain's resources, or the auth layers' admin rejection
    □ (∀ (r : Loc) (rq : IRRModel) (skip v3 : Bool) (af : GoFunc) (A : IProp GF)
        (B : Loc → IProp GF),
      {{ irrWrapperIs r rq skip ∗ A ∗
          ({{ chainRes c (.ok ai) ∗ A }} (App (App (Val #af) (Val #r)) (Val #v3))
            {{ (ar : Loc), RET #ar; chainRes c (.ok ai) ∗ B ar }}) }}
        (App (App (App (Val #(methods ai.ty go!"Apply" ai.v)) (Val #r)) (Val #v3)) (Val #af))
      {{ (ar : Loc), RET #ar;
          B ar ∨ (⌜needAdminPermission rq = true⌝ ∗ A ∗ rejectResultIs ar) }}))

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
  iprop(⌜opts.Logger' ≠ null⌝ ∗ isApplyKV opts.KV' E.s E.γ ∗ mvcc.hookIs E.γ E.P E.f ∗
    isApplyLessor opts.Lessor' E.γ E.P E.f ∗ isAuthStore opts.AuthStore' E.P E.f ∗
    isAlarmStore opts.AlarmStore' E.P E.f ∗ isCluster opts.Cluster' E.P E.f ∗
    isRaftStatus opts.RaftStatus' ∗ isSnapshotServer opts.SnapshotServer' ∗
    isConsistentIndexer opts.ConsistentIndex')

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

/-- The auth layer's mutex's resource: its `authInfo`. -/
def authInfoOwn (p : Loc) : IProp GF :=
  iprop(∃ info : go_etcd_io.etcd.server.v3.auth.AuthInfo,
    structFieldRef authApplierV3 go!"authInfo" p ↦ info)

/-- **The `*authApplierV3` `p`**: its inner applier, auth store and lessor, read-only, with
their contracts, and its mutex, whose resource is its `authInfo`. -/
def authIs (E : AEnv GF) (p : Loc) (inner : GoInterface) : IProp GF :=
  iprop(structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ∗
    (∃ st : GoInterface, structFieldRef authApplierV3 go!"as" p ↦□ st ∗ isAuthStore st E.P E.f) ∗
    (∃ le : GoInterface, structFieldRef authApplierV3 go!"lessor" p ↦□ le ∗
      isApplyLessor le E.γ E.P E.f) ∗
    sync.isMutex (structFieldRef authApplierV3 go!"mu" p) (authInfoOwn p))

instance authIs_persistent (E : AEnv GF) (p : Loc) (inner : GoInterface) :
    Persistent (authIs E p inner) := by
  unfold authIs; infer_instance

end defs

end apply
end EtcdGrove
end Perennial
