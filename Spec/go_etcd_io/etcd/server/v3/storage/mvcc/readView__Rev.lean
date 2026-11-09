/-
`(*readView).Rev()` (`kv_view.go:32`): `rv.kv.Read(SharedBufReadTxMode, traceutil.TODO())`, its
`Rev()`, its `End()`. Internal: the body of the store's promoted `Rev` (`KV.Rev.contract`); no client
holds a view. Proof sketch: `KV.Read.contract` at `kv` (the update fires at the read; 4b's `TODO()`
gives a fresh trace), `Txn.Rev.contract`, `Txn.End.contract` (`.read`: the token back), through
`shapes`.

**Changes** from `specs-ref`'s file: `KV.Rev.contract`'s statement at the view's store.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Rev`'s behaviour for the store the view reads. -/
def readView.Rev.spec : Prop :=
  ∀ (rv : Loc) (kv : GoInterface) (γ : MvccName) (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      rv.[readView, go!"kv"] ↦□ kv ∗ isMvcc kv γ ∗ mvccReaders γ 1 ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
  {{ (r : w64), RET #r; mvccReaders γ 1 ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.rev⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
