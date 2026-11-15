/-
`(*readView).FirstRev()` (`kv_view.go:26`): a read transaction's `FirstRev()`. Internal: the body
of the store's promoted `FirstRev` (`KV.FirstRev.contract`). Proof sketch: as `readView.Rev`, with
`Txn.FirstRev.contract` (`.read σ`: `σ.crev`).

**Changes** from `specs-ref`'s file: `KV.FirstRev.contract`'s statement at the view's store.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

/-- `KV.FirstRev`'s behaviour for the store the view reads. -/
def readView.FirstRev.spec : Prop :=
  ∀ (rv : Loc) (kv : GoInterface) (γ : MvccName) (rt : Bool) (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      rv.[readView, go!"kv"] ↦□ kv ∗ isMvcc kv γ ∗ revRd γ rt ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"FirstRev")) (Val #()))
  {{ (r : w64), RET #r; revRd γ rt ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.crev⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
