module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendGreaterOrEqual
public import Spec.k8s_io.utils.third_party.forked.golang.btree.empty
public import Spec.k8s_io.utils.third_party.forked.golang.btree.optional
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__iterate
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Read

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem BTree.AscendGreaterOrEqual.wp_proof (wp_empty : empty.spec (GF := GF) (hG := hG))
    (wp_optional : optional.spec (GF := GF) (hG := hG))
    (wp_iterate : node.iterate.spec (GF := GF) (hG := hG)) :
    BTree.AscendGreaterOrEqual.spec (GF := GF) (hG := hG) := by
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
    rw [show ascRange o.lt ([] : List (V × K)) (some kp) none = [] from rfl]
    iapply iterDone_nil $$ HI
  · ihave %Hnn := ownNode_not_null $$ Hn
    wp_if_destruct
    · exact absurd Hif Hnn
    subst Hel
    wp_apply wp_optional pivot
    wp_apply wp_empty
    ihave #Hks := optKey_optional o pivot kp $$ Hk1
    ihave #Hku := optKey_empty o
    wp_apply (wp_iterate o tv.cow' f less dq tv.root' tr (W64 1) _ _ (some kp) none true false
      iterator (ascRange o.lt tr.elems (some kp) none) [] I d h Hsh Hsorted (Or.inl rfl)
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

end btree
end EtcdGrove
end Perennial
