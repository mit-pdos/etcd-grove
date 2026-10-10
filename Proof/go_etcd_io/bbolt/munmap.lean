module
public import Spec.go_etcd_io.bbolt.munmap
public import Spec.golang_org.x.sys.unix.Munmap

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

theorem munmap.wp_proof (hMunmap : unix.Munmap.spec (GF := GF) (hG := hG)) :
    munmap.spec (GF := GF) (hG := hG) := by
  intro dbl d fd bs n
  wp_start as ⟨Hdb, Hf, Hm⟩
  wp_auto
  wp_if_destruct
  · icases Hm with (⟨-, Hm⟩ | ⟨%Hc, -⟩)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true Hif)]
      iapply HΦ; iframe
    · exfalso; exact Hc.1 (by rw [Hif]; rfl)
  icases Hm with (⟨%Hnil, -⟩ | ⟨%Hc, Hmap, Hrange⟩)
  · exact absurd Hnil Hif
  try wp_auto
  wp_apply hMunmap fd bs d.dataref' n Hc.2.1 Hc.2.2 $$ [Hf Hmap Hrange] as ⟨Hf, Hmap⟩
  · iframe
  try wp_auto
  rw [ite_eq_right_of_eq_false _ _ (eq_false Hif)]
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
