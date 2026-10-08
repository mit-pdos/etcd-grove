import EtcdGrove.Btree.Spec.BTreeG__AscendRange
import EtcdGrove.Btree.Spec.optional
import EtcdGrove.Btree.Spec.node__iterate
import EtcdGrove.Btree.Lemmas.Read

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

theorem BTreeG.AscendRange.wp_proof (wp_optional : optional.spec (GF := GF) (hG := hG))
    (wp_iterate : node.iterate.spec (GF := GF) (hG := hG)) :
    BTreeG.AscendRange.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t dq s greaterOrEqual kge lessThan klt iterator I
  wp_start as ⟨Ht, #Hk1, #Hk2, #Hiter, HI⟩
  unfold ownBTree
  icases Ht with ⟨%tv, %f, %less, %d, Ht, #Hcow, %Hdeg, %Hlen, %Hsorted, #Hitems, Hroot⟩
  icases btree_fields $$ Ht with ⟨Hdg, Hln, Hrt, Hcw, Hback⟩
  wp_auto
  unfold ownRoot
  icases Hroot with (%Hnil | ⟨%h, %tr, ⟨%Hsh, %Hrb, %Hel⟩, Hn⟩)
  · obtain ⟨Hr, rfl⟩ := Hnil
    rw [Hr]
    wp_auto
    iapply HΦ
    isplitr [HI]
    · iexists tv, f, less, d
      iframe Hcow Hitems
      isplitl [Hback Hdg Hln Hrt Hcw]
      · iapply Hback; iframe
      iframe %Hdeg %Hlen %Hsorted
      ileft; ipureintro; exact ⟨Hr, rfl⟩
    rw [show ascRange o.lt ([] : List (V × K)) (some kge) (some klt) = [] from rfl]
    iapply iterDone_nil $$ HI
  · ihave %Hnn := ownNode_not_null $$ Hn
    wp_if_destruct
    · exact absurd Hif Hnn
    subst Hel
    wp_apply wp_optional greaterOrEqual
    wp_apply wp_optional lessThan
    ihave #Hks := optKey_optional o greaterOrEqual kge $$ Hk1
    ihave #Hku := optKey_optional o lessThan klt $$ Hk2
    wp_apply (wp_iterate o tv.cow' f less dq tv.root' tr (W64 1) _ _ (some kge) (some klt) true false
      iterator (ascRange o.lt tr.elems (some kge) (some klt)) [] I d h Hsh Hsorted (Or.inl rfl)
      (fun _ => rfl) (fun _ h => absurd h (by simp))
      (by simp)) $$ [Hn HI] as %hit' %ok ⟨Hn, Hpost⟩
    · iframe # ∗
    iapply HΦ
    isplitr [Hpost]
    · iexists tv, f, less, d
      iframe Hcow Hitems
      isplitl [Hback Hdg Hln Hrt Hcw]
      · iapply Hback; iframe
      iframe %Hdeg %Hlen %Hsorted
      iright; iexists h, tr; iframe; ipureintro; exact ⟨Hsh, Hrb, rfl⟩
    iapply iterDone_of_iterate _ _ (by simp) $$ Hpost

end proof

end Btree
end EtcdGrove
end Perennial
