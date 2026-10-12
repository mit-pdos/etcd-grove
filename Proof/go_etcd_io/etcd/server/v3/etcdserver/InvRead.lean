/-
The request path's read side (`v3_server.go`'s `Range`, the read-only `Txn`, `doSerialize`,
`LinearizableReadNotify`; the getters of the response header): the shared vocabulary of their
specs. Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12); plan:
`notes/decisions.md`, "The request path".

**The server, as a reader sees it** (`isServerRead s E γr`, persistent): the fields the read side
reads besides `isServerReq`'s: the read loop (`read`, its contract `isRead`), the KV (`kv`: the
bare store of the applier's environment `E`, the apply package's standing premise `txn.isKV`;
its `ReadView` for `KV().Rev()`), the lessor (`apply.isApplyLessor`: `CheckTxnAuth` and the
txn package's `checkTxn`), the auth store (`apply.isAuthStore`: `IsRangePermitted`,
`CheckTxnAuth`'s checks, `Revision`), the logger (`lg`, not nil), the configuration's
`WarningApplyDuration`, the term's atomic (`Term`), a certificate of a log of `NewStore`'s two
revisions (`idxCert`: every read is of a log at least that long, so a read's revision is not
`0`), and **the store stays small** (`storeSmall`: every certified log has at most `2 ^ 62`
changes, `txn.LogSmall`, the sort's premise; a premise, as the apply thread's `rangeOk`/`TxnPre`
of its entries).

**A read call's resources** (`srvRdCall s E γr c`, ctx-independent): the store's reader slots
(`mvcc.storeReader`: its `RWMutex`es admit a bounded number of readers), a reader slot of the
logger's lock (`srvLgReader`), and a lower bound `c` of the cluster's committed index the caller
knew of (`committedAtLeast`: what a linearizable read's `readIndexOk` is relative to).

**The read side's answers**: a successful `Range` of `o` (`rangeReadOk`: the txn package's
`rangeResult` with no error at a certified log of at least two revisions, read after the read
index if linearizable, the response header's id fields owned), a successful read-only `Txn`
(`txnReadOk`); a successful writing `Txn` (`txnAppliedOk`, as `Put`'s and `DeleteRange`'s: the
apply thread's application of the request the proposed data decode to), its failure
(`txnErrOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The store stays small** (persistent; a premise): every certified log has at most `2 ^ 62`
changes (`txn.LogSmall`: the sort's premise, `sort.Sort`'s bound and the comparators'
non-negative values). -/
def storeSmall (γ : mvcc.StoreNames) : IProp GF :=
  iprop(□ ∀ log : mvcc.Log, mvcc.idxCert γ.idx log -∗ ⌜txn.LogSmall log⌝)

instance storeSmall_persistent (γ : mvcc.StoreNames) : Persistent (storeSmall (GF := GF) γ) := by
  unfold storeSmall; infer_instance

/-- The values of the server's fields the read side reads (besides `ReqFields`). -/
structure ReadFields where
  read : Loc
  kv : GoInterface
  lessor : GoInterface
  auth : GoInterface
  lg : Loc
  wad : w64
  rv : Loc

/-- **The server `s` as a reader sees it** at the fields' values `v` (persistent; see the file
header). -/
def srvReadFieldsAt (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v : ReadFields) : IProp GF :=
  iprop(srvReadAddr s ↦□ v.read ∗ isRead v.read γr ∗
    srvKVAddr s ↦□ v.kv ∗ txn.isKV v.kv E.s E.γ ∗
    E.s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
        #v.rv : GoInterface) ∗
    mvcc.isReadView v.rv E.s E.γ ∗
    srvLessorAddr s ↦□ v.lessor ∗ apply.isApplyLessor v.lessor E.γ E.P E.f ∗
    srvAuthStoreAddr s ↦□ v.auth ∗ apply.isAuthStore v.auth E.P E.f ∗
    srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
    srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ v.wad ∗
    inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    storeSmall E.γ ∗
    (∃ log₀ : mvcc.Log, mvcc.idxCert E.γ.idx log₀ ∗ ⌜2 ≤ log₀.length⌝))

instance srvReadFieldsAt_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (v : ReadFields) : Persistent (srvReadFieldsAt s E γr v) := by
  unfold srvReadFieldsAt; infer_instance

/-- **The server `s`, as a reader sees it** (persistent). -/
def isServerRead (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ v : ReadFields, srvReadFieldsAt s E γr v)

instance isServerRead_persistent (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (isServerRead s E γr) := by
  unfold isServerRead; infer_instance

/-- **A read call's resources** (see the file header): the store's reader slots, a reader slot
of `s.lgMu`, and the committed index `c` the caller knew of. -/
def srvRdCall (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ committedAtLeast γr c)

/-- **A successful `Range` of `o`** with the response `resp`: the txn package's answer with no
error (`rangeResult`: the server's selection of the state at the revision read) at a certified
log `log` of at least `NewStore`'s two revisions (so the header's revision, `log`'s last, is not
`0`), read after the read index if the request is linearizable (`readIndexOk γr c`: the applied
index reached the committed index `c` the caller knew of), the response header's id fields
owned. -/
def rangeReadOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (o : OpFull) (resp : Loc) :
    IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ ∗
    (if o.base.serializable then iprop(True) else readIndexOk γr c) ∗
    txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp))

/-- **A successful read-only `Txn` of `t`** (as `rangeReadOk`): the server's run of `t` on the
state after a certified log `log` (`srvRunTxn`: its verdict and results, no change), the
response's header revision `log`'s last, read after the read index unless every get is
serializable (`txnSerializable`), the header's id fields owned. -/
def txnReadOk (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (t : TxnModel) (resp : Loc) :
    IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63⌝ ∗
    (if txn.txnSerializable t then iprop(True) else readIndexOk γr c) ∗
    txn.txnResponseIs false resp (W64 ((log.length : Int) - 1)) t
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
      (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp))

/-- **A successful writing `Txn` of `t`** (as `Put`'s and `DeleteRange`'s): the request the
proposed data decode to (`rq'`, whose transaction `t'` is `t` unless a range end is `[0]`,
`irrWireOf`) was dispatched by the apply thread at the KV state `x` to `x'` and applied
(`applied l false`), possibly with header-only ranges (`skip`: `SkipRangeExecution`, the apply
thread's `IsRegistered` being "some boolean" in the wait's contract), the response the
transaction's (`txnOutcomeIs` at `x.log`), the header's id fields owned (`appliedHdr`), mvcc's
certificate of the log after. -/
def txnAppliedOk (E : apply.AEnv GF) (t : TxnModel) (resp : Loc) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (t' : TxnModel)
      (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq' ∧ rq'.txn = some t' ∧
      (irrNoZeroEnd (irrTxn t) → t' = t) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)⌝ ∗
    apply.txnOutcomeIs x.log t' skip resp GoInterface.nil (.applied l false) ∗
    apply.appliedHdr x.log (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
    mvcc.idxCert E.γ.idx x'.log)

/-- **A failed writing `Txn` of `t`** (as `Put`'s): the apply thread's error (`appliedErr`), or
the proposal's (made or not; if made, deposited: it may still be applied). -/
def txnErrOk (E : apply.AEnv GF) (ρ : ReqNames) (t : TxnModel) (err : GoInterface) : IProp GF :=
  iprop((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
      ⌜irrWireOf (apply.withHeader (irrTxn t) hm) rq'⌝ ∗ appliedErr E rq' err) ∨
    srvMaybeDeposited ρ (irrTxn t))

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions]

/-- **A `fmt.Errorf` error is one the gRPC layer can take** (`applyErrIs`), given the method-set
fact that `*errors.errorString` is a leaf error type (the server's package facts, `srvErrVars`). -/
theorem applyErrIs_errorf (err : GoInterface)
    (hleaf : ∀ x : Loc, errLeaf ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩) :
    mvcc.errorfIs (GF := GF) err ⊢ applyErrIs err := by
  iunfold mvcc.errorfIs
  iintro ⟨%x, %h, #He⟩
  subst h
  iapply applyErrIs_leaf _ (hleaf x)
  iunfold errMsgOk
  iintro !> %Φ - HΦ
  iapply He
  inext
  iintro %str
  iapply HΦ
  itrivial

end lemmas

end EtcdGrove
end Perennial
