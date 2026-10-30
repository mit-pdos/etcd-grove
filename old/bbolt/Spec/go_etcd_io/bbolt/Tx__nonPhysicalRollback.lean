module
public import Spec.go_etcd_io.bbolt.Tx__close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

variable [AllG GF]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `tx.nonPhysicalRollback()` of an open read transaction: `close`. -/
abbrev Tx.nonPhysicalRollback.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) (txl : Loc) (k : Nat)
    (r : Reader) (m : Bool),
  I.RemoveReadonlySpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ ∗ ownReadTx dbl γ txl k r σ.data σ.ps m }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"nonPhysicalRollback")) (Val #()))
  {{ RET #(); ∃ (ro : List w64) (t : Tx), ⌜σ.readers !! k = some r⌝ ∗
      ownDB I dbl γ (σ.removeReader k r ro) ∗ txl ↦ t ∗ ⌜t.db' = null⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
