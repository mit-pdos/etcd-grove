/-
`t.UnsafeDelete(bucket, k)` (`batch_tx.go:228-245`): translated; internal. bbolt's `Delete` (a
missing bucket or an error: `lg.Fatal`), `pending++`. Changes: over `btPhys`. Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`t.UnsafeDelete(bk, k)`** on the embedded `batchTx`: bbolt's write transaction at `del`. -/
def batchTx.UnsafeDelete.spec : Prop :=
  ∀ (γ : BeNames) (I : Image) (n d : Nat) (bk : GoInterface) (bi : BktInfo) (ks : GoSlice)
    (dk : DFrac) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ btPhys γ I n d ∗ bucketOk bk bi ∗ ks ↦*{dk} k }}
    (App (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #ks))
  {{ RET #(); btPhys γ (I.del bi.name k) (n + 1) d ∗ ks ↦*{dk} k }}

end spec

end Backend
end EtcdGrove
end Perennial
