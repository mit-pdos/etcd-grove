import EtcdGrove.Btree.Spec.BTreeG__Get
import EtcdGrove.Btree.Spec.node__get
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

theorem BTreeG.Get.wp_proof (wp_get : node.get.spec (GF := GF) (hG := hG)) :
    BTreeG.Get.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t dq s key k
  wp_start as ⟨Ht, #Hk⟩
  unfold ownBTree
  icases Ht with ⟨%tv, %f, %less, %d, Ht, #Hcow, %Hdeg, %Hlen, %Hsorted, #Hitems, Hroot⟩
  icases btree_fields $$ Ht with ⟨Hdg, Hln, Hrt, Hcw, Hback⟩
  wp_alloc_anon
  wp_pures
  wp_alloc_anon
  wp_auto
  unfold ownRoot
  icases Hroot with (%Hnil | ⟨%h, %tr, ⟨%Hsh, %Hrb, %Hel⟩, Hn⟩)
  · obtain ⟨Hr, rfl⟩ := Hnil
    rw [Hr]
    wp_auto
    simp only [lookup, List.find?_nil, Option.map_none, Option.getD_none, Option.isSome_none]
    iapply HΦ
    iexists tv, f, less, d
    iframe Hcow Hitems
    isplitl [Hback Hdg Hln Hrt Hcw]
    · iapply Hback; iframe
    iframe %Hdeg %Hlen %Hsorted
    ileft; ipureintro; exact ⟨Hr, trivial⟩
  · ihave %Hnn := ownNode_not_null $$ Hn
    wp_if_destruct
    · exact absurd Hif Hnn
    · subst Hel
      wp_apply wp_get o tv.cow' f less dq tv.root' tr key k d h Hsh Hsorted $$ [Hn] as Hn
      · iframe # ∗
      iapply HΦ
      iexists tv, f, less, d
      iframe Hcow Hitems
      isplitl [Hback Hdg Hln Hrt Hcw]
      · iapply Hback; iframe
      iframe %Hdeg %Hlen %Hsorted
      iright; iexists h, tr; iframe; ipureintro; exact ⟨Hsh, Hrb, rfl⟩

end proof

end Btree
end EtcdGrove
end Perennial
