import EtcdGrove.Btree.Spec.BTreeG__Clone
import EtcdGrove.Btree.NodeLemmas
import EtcdGrove.Btree.Lemmas.Struct

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

theorem BTreeG.Clone.wp_proof : BTreeG.Clone.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t s
  wp_start as Ht
  iNamed Ht
  ihave #Hcp : (tv.cow' ↦□ (copyOnWriteContext.mk f less : copyOnWriteContext V) : IProp GF) $$ []
  · unfold isCow; icases Hcow with ⟨#H, -, -⟩; iexact H
  ihave #Hfl : isFreeList (V := V) f $$ []
  · unfold isCow; icases Hcow with ⟨-, #H, -⟩; iexact H
  ihave #Hless : isLess o less $$ []
  · unfold isCow; icases Hcow with ⟨-, -, #H⟩; iexact H
  iapply wp_fupd
  wp_auto
  imod ownRoot_clone o _ f less cow1_ptr cow2_ptr _ _ d _ s $$ [$Hcow $cow1 $cow2 $Hroot]
    with ⟨cow1, cow2, Hr1, Hr2⟩
  ipersist cow1
  ipersist cow2
  ihave #Hc1 : isCow o cow1_ptr f less $$ []
  · unfold isCow; iframe cow1 Hfl Hless
  ihave #Hc2 : isCow o cow2_ptr f less $$ []
  · unfold isCow; iframe cow2 Hfl Hless
  imodintro
  iapply HΦ
  unfold ownBTree
  isplitl [Ht Hr1]
  · iexists _, f, less, d
    iframe Ht Hr1 Hitems
    iframe Hc1
    ipureintro; exact ⟨Hdeg, Hlen, Hsorted⟩
  · iexists _, f, less, d
    iframe out Hr2 Hitems
    iframe Hc2
    ipureintro; exact ⟨Hdeg, Hlen, Hsorted⟩

end proof

end Btree
end EtcdGrove
end Perennial
