/-
`NewHashMapFreelist()` (U2 internal): a fresh, empty hash map freelist with no reader.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.newShared

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

abbrev NewHashMapFreelist.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist }}
    (App (Val #(functions go_etcd_io.bbolt.internal.freelist.NewHashMapFreelist [])) (Val #()))
  {{ (fli : GoInterface), RET #fli; ⌜fli ≠ interface.nil⌝ ∗ flPgOwn fli FLPg.empty ∗
      flRoOwn fli [] }}

theorem NewHashMapFreelist.wp_proof : NewHashMapFreelist.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
