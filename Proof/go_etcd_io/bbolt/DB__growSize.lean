module
public import Spec.go_etcd_io.bbolt.DB__growSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.growSize.wp_proof : DB.growSize.spec (GF := GF) (hG := hG) := by
  intro dbl d dq mmapSize growSize
  wp_start as Hl
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true Hif)]
    iapply HΦ $$ Hl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false Hif)]
    iapply HΦ $$ Hl

end proof

end bbolt
end EtcdGrove
end Perennial
