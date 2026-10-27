module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.NewWithFreeList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem NewWithFreeList.wp_proof : NewWithFreeList.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o degree less f Hd1 Hd2
  wp_start as ⟨#Hless, #Hfl⟩
  iapply wp_fupd
  wp_auto
  wp_if_destruct
  · exfalso; word
  irename «$v1» => Hc
  ipersist Hc
  irename «$r0» => Ht
  generalize «$r0_ptr» = t at *
  imodintro
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

end btree
end EtcdGrove
end Perennial
