/- Lean-first (no Rocq counterpart). The proof of `pickMeta`: order the metas by txid, then take the first valid one. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pickMeta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__validate

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

theorem pickMeta.wp_proof (wp_validate : Meta.validate.spec (GF := GF) (hG := hG)) :
    pickMeta.spec (GF := GF) (hG := hG) := by
  intro m0 m1 v0 v1 dq0 dq1
  wp_start as ⟨H0, H1, %Hpos⟩
  have hn0 : m0 ≠ null := by intro h; subst h; simp [null] at Hpos
  have hn1 : m1 ≠ null := by intro h; subst h; simp [null] at Hpos
  icases typedPointsto_split _ _ _ $$ H0 with H0
  icases typedPointsto_split _ _ _ $$ H1 with H1
  simp only [TypedPointsto.typedPointstoDef]
  icases H0 with ⟨H0magic, H0version, H0pageSize, H0flags, H0root, H0freelist, H0pgid, H0txid, H0checksum, -⟩
  icases H1 with ⟨H1magic, H1version, H1pageSize, H1flags, H1root, H1freelist, H1pgid, H1txid, H1checksum, -⟩
  (try wp_auto)
  ihave H0 : m0 ↦{dq0} v0 $$ [H0magic H0version H0pageSize H0flags H0root H0freelist H0pgid H0txid H0checksum]
  · iapply typedPointsto_combine _ _ _ hn0
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave H1 : m1 ↦{dq1} v1 $$ [H1magic H1version H1pageSize H1flags H1root H1freelist H1pgid H1txid H1checksum]
  · iapply typedPointsto_combine _ _ _ hn1
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_if_destruct
  · (try wp_auto)
    wp_apply wp_validate m1 v1 dq1 $$ [H1] as H1
    · iframe H1; ipureintro; exact Hpos.2
    wp_if_destruct
    · (try wp_auto)
      rw [show pickMetaRes m0 v0 m1 v1 = m1 by simp [pickMetaRes, pickValid, *]]
      iapply HΦ; iframe
    · (try wp_auto)
      wp_apply wp_validate m0 v0 dq0 $$ [H0] as H0
      · iframe H0; ipureintro; exact Hpos.1
      wp_if_destruct
      · (try wp_auto)
        rw [show pickMetaRes m0 v0 m1 v1 = m0 by simp [pickMetaRes, pickValid, *]]
        iapply HΦ; iframe
      · (try wp_auto)
        rw [show pickMetaRes m0 v0 m1 v1 = null by simp [pickMetaRes, pickValid, *]]
        iapply HΦ; iframe
  · (try wp_auto)
    wp_apply wp_validate m0 v0 dq0 $$ [H0] as H0
    · iframe H0; ipureintro; exact Hpos.1
    wp_if_destruct
    · (try wp_auto)
      rw [show pickMetaRes m0 v0 m1 v1 = m0 by simp [pickMetaRes, pickValid, *]]
      iapply HΦ; iframe
    · (try wp_auto)
      wp_apply wp_validate m1 v1 dq1 $$ [H1] as H1
      · iframe H1; ipureintro; exact Hpos.2
      wp_if_destruct
      · (try wp_auto)
        rw [show pickMetaRes m0 v0 m1 v1 = m1 by simp [pickMetaRes, pickValid, *]]
        iapply HΦ; iframe
      · (try wp_auto)
        rw [show pickMetaRes m0 v0 m1 v1 = null by simp [pickMetaRes, pickValid, *]]
        iapply HΦ; iframe


end proof

end bboltfs
end EtcdGrove
end Perennial
