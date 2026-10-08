import EtcdGrove.Btree.Spec.BTreeG__DescendGreaterThan
import EtcdGrove.Btree.Spec.empty
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

theorem BTreeG.DescendGreaterThan.wp_proof (wp_empty : empty.spec (GF := GF) (hG := hG))
    (wp_optional : optional.spec (GF := GF) (hG := hG))
    (wp_iterate : node.iterate.spec (GF := GF) (hG := hG)) :
    BTreeG.DescendGreaterThan.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t dq s pivot kp iterator I
  wp_start as ⟨Ht, #Hk1, #Hiter, HI⟩
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
    rw [show descRange o.lt ([] : List (V × K)) none (some kp) = [] from rfl]
    iapply iterDone_nil $$ HI
  · ihave %Hnn := ownNode_not_null $$ Hn
    wp_if_destruct
    · exact absurd Hif Hnn
    subst Hel
    wp_apply wp_empty
    wp_apply wp_optional pivot
    ihave #Hks := optKey_empty o
    ihave #Hku := optKey_optional o pivot kp $$ Hk1
    wp_apply (wp_iterate o tv.cow' f less dq tv.root' tr (W64 (-1)) _ _ none (some kp) false false
      iterator (descRange o.lt tr.elems none (some kp)) [] I d h Hsh Hsorted (Or.inr rfl)
      (fun h => absurd h (by simp)) (fun _ h => absurd h (by simp))
      (by rw [ite_eq_right (by decide)]; simp)) $$ [Hn HI] as %hit' %ok ⟨Hn, Hpost⟩
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
