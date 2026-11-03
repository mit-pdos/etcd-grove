/- Lean-first (no Rocq counterpart). The proof of `(*Meta).validate`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__validate
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__sum64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem Meta.validate.wp_proof (wp_sum64 : Meta.sum64.spec (GF := GF) (hG := hG)) :
    Meta.validate.spec (GF := GF) (hG := hG) := by
  intro m v dq
  wp_start as ⟨Hm, %Hpos⟩
  have hnn : m ≠ null := by intro h; subst h; simp [null] at Hpos
  icases typedPointsto_split _ _ _ $$ Hm with Hm
  simp only [TypedPointsto.typedPointstoDef]
  icases Hm with ⟨Hmagic, Hversion, HpageSize, Hflags, Hroot, Hfreelist, Hpgid, Htxid, Hchecksum, -⟩
  wp_auto
  wp_if_destruct
  · have Hmg := Hif
    wp_if_destruct
    · ihave Hm : m ↦{dq} v $$ [Hmagic Hversion HpageSize Hflags Hroot Hfreelist Hpgid Htxid Hchecksum]
      · iapply typedPointsto_combine _ _ _ hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      wp_apply wp_sum64 m v dq $$ [Hm] as Hm
      · iframe Hm; ipureintro; exact Hpos
      rw [show decide (metaValid v) =
        decide (v.checksum' = metaSum v) by simp [metaValid, Hmg, Hif]]
      iapply HΦ $$ Hm
    · rw [decide_eq_false (fun (h : metaValid v) => Hif h.2.1)]
      iapply HΦ
      iapply typedPointsto_combine _ _ _ hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
  · rw [decide_eq_false (fun (h : metaValid v) => Hif h.1)]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end bboltfs
end EtcdGrove
end Perennial
