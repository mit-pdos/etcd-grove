/-
`(*readView).Range(ctx, key, end, ro)` (`kv_view.go:38`): a `ConcurrentReadTxMode` read transaction's
`Range`, then `End`. Internal: the body of the store's promoted `Range` (`KV.Range.contract`; users:
the apply's `Compaction` header, `apply/backend.go:78`; the watch's `prevKV`, 3f/2b). Proof sketch:
`KV.Read.contract` at `kv`, `Txn.Range.contract` (`.read σ`: over `σ.kv`), `Txn.End.contract`.

**Changes** from `specs-ref`'s file: `KV.Range.contract`'s statement at the view's store.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Range`'s behaviour for the store the view reads. -/
def readView.Range.spec : Prop :=
  ∀ (rv : Loc) (kv : GoInterface) (γ : MvccName) (ctx : GoInterface) (key endk : GoSlice)
    (kk e : Bytes) (dk de : DFrac) (ro : RangeOptions) (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      rv.[readView, go!"kv"] ↦□ kv ∗ isMvcc kv γ ∗ mvccReaders γ 1 ∗ Context.ctxOk ctx ∗
      key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
      (Val #ctx)) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); mvccReaders γ 1 ∗
      key ↦*{dk} kk ∗ endk ↦*{de} e ∗ ∃ (σ : MvccState) (out : RangeOut), Q σ ∗
        ⌜rangeOut σ.kv σ.crev (mrange kk endk e) ro out⌝ ∗ rangeResOwn ctx r err out }}

end spec
end Mvcc
end EtcdGrove
end Perennial
