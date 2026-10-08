import EtcdGrove.Btree.Spec.NewWithFreeListG

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

theorem NewWithFreeListG.wp_proof : NewWithFreeListG.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o degree less f Hd1 Hd2
  wp_start as ⟨#Hless, #Hfl⟩
  wp_auto
  wp_if_destruct
  · exfalso; word
  irename «$v1» => Hc
  ipersist Hc
  wp_alloc t as Ht
  wp_auto
  iapply HΦ
  unfold ownBTree
  iexists _, f, less, sint.nat degree
  iframe Ht
  unfold named
  isplitr
  · unfold isCow
    isplitr; · iexact Hc
    isplitr; · iexact Hfl
    iexact Hless
  isplitr
  · ipureintro; refine ⟨by word, by word, by word⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; simp [Sorted]
  isplitr
  · unfold allItems; imodintro; iintro %e %he; simp at he
  unfold ownRoot
  ileft; ipureintro; exact ⟨rfl, rfl⟩

end proof

end Btree
end EtcdGrove
end Perennial
