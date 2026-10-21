/-
Lean-first (no Rocq counterpart).

The proof of `resEqual`: by the kinds.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.resEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem resEqual.wp_proof (wp_vrEqual : vrEqual.spec (GF := GF) (hG := hG)) :
    resEqual.spec (GF := GF) (hG := hG) := by
  intro x y
  wp_start
  wp_auto
  wp_if_destruct
  · have Hk := Hif; clear Hif
    wp_if_destruct
    · have Hk0 := Hif; clear Hif
      wp_if_destruct
      · have Hf := Hif; clear Hif
        cases hxf : x.Found'
        · try wp_auto
          rw [show resEqualL x y = true by
            unfold resEqualL; rw [if_neg (fun h => h Hk), if_pos Hk0]; simp [← Hf, hxf]]
          iapply HΦ; itrivial
        · try wp_auto
          wp_apply wp_vrEqual x.R' y.R'
          rw [show resEqualL x y = decide (x.R' = y.R') by
            unfold resEqualL; rw [if_neg (fun h => h Hk), if_pos Hk0]; simp [← Hf, hxf]]
          iapply HΦ; itrivial
      · rw [show resEqualL x y = false by
          unfold resEqualL; rw [if_neg (fun h => h Hk), if_pos Hk0]; simp [Hif]]
        iapply HΦ; itrivial
    · have Hk0 := Hif; clear Hif
      wp_if_destruct
      · rw [show resEqualL x y = decide (x.N' = y.N') by
          unfold resEqualL; rw [if_neg (fun h => h Hk), if_neg Hk0, if_pos Hif]]
        iapply HΦ; itrivial
      · rw [show resEqualL x y = true by
          unfold resEqualL; rw [if_neg (fun h => h Hk), if_neg Hk0, if_neg Hif]]
        iapply HΦ; itrivial
  · rw [show resEqualL x y = false by unfold resEqualL; rw [if_pos Hif]]
    iapply HΦ; itrivial

end proof

end linkvtxn
end EtcdGrove
end Perennial
