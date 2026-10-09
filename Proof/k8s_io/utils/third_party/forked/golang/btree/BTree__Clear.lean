module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clear
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__reset

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

theorem BTree.Clear.wp_proof
    (wp_node_reset : node.reset.spec (GF := GF) (hG := hG)) :
    BTree.Clear.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t s add
  wp_start as Hown
  unfold ownBTree
  iNamed Hown
  wp_auto
  by_cases hr : tv.root' = null
  · rw [decide_eq_true hr]
    wp_auto
    iapply HΦ
    iexists _, f, less, d
    iframe Ht
    unfold named
    isplitr; · iexact Hcow
    isplitr; · ipureintro; exact Hdeg
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; simp [Sorted]
    isplitr; · unfold allItems; imodintro; iintro %e %he; simp at he
    unfold ownRoot
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · rw [decide_eq_false hr]
    cases add
    · wp_auto
      iapply HΦ
      iexists _, f, less, d
      iframe Ht
      unfold named
      isplitr; · iexact Hcow
      isplitr; · ipureintro; exact Hdeg
      isplitr; · ipureintro; rfl
      isplitr; · ipureintro; simp [Sorted]
      isplitr; · unfold allItems; imodintro; iintro %e %he; simp at he
      unfold ownRoot
      ileft; ipureintro; exact ⟨rfl, rfl⟩
    · wp_auto
      unfold ownRoot
      icases Hroot with (%Hn | ⟨%h, %tr, %_, Hn⟩)
      · exact absurd Hn.1 hr
      wp_apply (wp_node_reset (V := V) (T := T) o tv.cow' f less tv.root' tr) $$ [Hn] as %b _
      · iframe Hn; iexact Hcow
      iapply HΦ
      iexists _, f, less, d
      iframe Ht
      unfold named
      isplitr; · iexact Hcow
      isplitr; · ipureintro; exact Hdeg
      isplitr; · ipureintro; rfl
      isplitr; · ipureintro; simp [Sorted]
      isplitr; · unfold allItems; imodintro; iintro %e %he; simp at he
      ileft; ipureintro; exact ⟨rfl, rfl⟩

end proof

end btree
end EtcdGrove
end Perennial
