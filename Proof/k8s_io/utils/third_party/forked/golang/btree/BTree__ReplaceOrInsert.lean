module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__maxItems
public import Spec.k8s_io.utils.third_party.forked.golang.btree.copyOnWriteContext__newNode
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__mutableFor
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__split
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__insert
public import Proof.k8s_io.utils.third_party.forked.golang.btree.NodeLemmas
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Lemmas.Insert

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree
open InsertLemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

set_option hygiene false in
/-- The common tail of `ReplaceOrInsert`: insert into the (owned, not full) root `r0`. -/
local macro "roi_tail" : tactic => `(tactic| (
  wp_apply wp_maxItems t (DFrac.own 1) ⟨tv.degree', tv.length', r0, tv.cow'⟩ $$ [Ht] as Ht
  · iexact Ht
  wp_apply wp_insert o tv.cow' f less r0 t0 item k _ d h0 tS0 (tE0 ▸ Hsorted) tL0 hmx Hdeg.2.1
      Hdeg.2.2 $$ [Hn] as %old %fnd ⟨%t', Hn, % ⟨ht1, ht2, ht3, ht4, ht5, ht6⟩⟩
  · iframe Hn Hcow Hitem
    rw [tE0]; iexact Hitems
  rw [tE0] at ht2 ht5 ht6
  have hsi := model_sorted_insert o.order s (item, k) Hsorted
  have hli := model_length_insert o.order s (item, k) Hsorted
  ihave #Hitems' : allItems o (insert o.lt s (item, k)) $$ []
  · unfold allItems
    imodintro
    iintro %e %he
    rcases model_mem_insert s (item, k) e he with he | rfl
    · iapply Hitems $$ %e %he
    · iexact Hitem
  subst ht5 ht6
  have hrb' : Tree.RootBounds d h0 t' := ⟨by omega, fun hp => by have := tRB0 hp; omega⟩
  ihave Hn := ownNode_of_owned o _ _ _ _ _ _ $$ Hn
  cases hlk : lookup s k with
  | none =>
    simp only [hlk, Option.isSome_none, Option.getD_none, Bool.false_eq_true, ↓reduceIte] at hli ⊢
    wp_auto
    iapply HΦ
    iexists ⟨tv.degree', tv.length' + W64 1, r0, tv.cow'⟩, f, less, d
    have Hl1 : tv.length' + W64 1 = W64 ↑(insert o.lt s (item, k)).length := by
      rw [Hlen, hli]; word
    iframe Ht Hcow Hitems' %Hdeg %Hl1 %hsi
    iright
    iexists h0, t'
    iframe Hn
    first | done | (ipureintro; exact ⟨ht1, hrb', ht2⟩)
  | some v =>
    simp only [hlk, Option.isSome_some, Option.getD_some, ↓reduceIte, Nat.add_zero] at hli ⊢
    wp_auto
    iapply HΦ
    iexists ⟨tv.degree', tv.length', r0, tv.cow'⟩, f, less, d
    have Hl1 : tv.length' = W64 ↑(insert o.lt s (item, k)).length := by
      rw [Hlen, hli]
    iframe Ht Hcow Hitems' %Hdeg %Hl1 %hsi
    iright
    iexists h0, t'
    iframe Hn
    first | done | (ipureintro; exact ⟨ht1, hrb', ht2⟩)))

theorem BTree.ReplaceOrInsert.wp_proof
    (wp_maxItems : BTree.maxItems.spec (GF := GF) (hG := hG))
    (wp_newNode : copyOnWriteContext.newNode.spec (GF := GF) (hG := hG))
    (wp_mutableFor : node.mutableFor.spec (GF := GF) (hG := hG))
    (wp_split : node.split.spec (GF := GF) (hG := hG))
    (wp_insert : node.insert.spec (GF := GF) (hG := hG)) :
    BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t s item k
  wp_start as ⟨Ht, #Hitem⟩
  unfold ownBTree
  icases Ht with ⟨%tv, %f, %less, %d, Ht, #Hcow, %Hdeg, %Hlen, %Hsorted, #Hitems, Hroot⟩
  wp_alloc_anon
  wp_pures
  wp_alloc_anon
  wp_auto
  unfold ownRoot
  icases Hroot with (%Hnil | ⟨%h, %tr, ⟨%Hsh, %Hrb, %Hel⟩, Hn⟩)
  · obtain ⟨Hr, rfl⟩ := Hnil
    rw [Hr]
    wp_auto
    wp_apply (wp_newNode (V := V) (K := K) (T := T) o tv.cow' f less) $$ [] as %r Hr
    · iexact Hcow
    unfold nodeShallow nodeFields
    icases Hr with ⟨%isl, %csl, ⟨%Hrn, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
    wp_auto
    wp_apply wp_slice_literal (l := [item])
    isplitr
    · ipureintro; rfl
    iintro %zsl ⟨Hz, -⟩
    wp_auto
    simp only [List.map_nil]
    wp_apply wp_slice_append $$ [$Hisl $Hicap $Hz] as %isl' ⟨Hisl, Hicap, -⟩
    simp only [lookup, List.find?_nil, Option.map_none, Option.getD_none, Option.isSome_none]
    iapply HΦ
    iexists ⟨tv.degree', tv.length' + W64 1, r, tv.cow'⟩, f, less, d
    simp only [insert, List.nil_append, List.length_singleton]
    iframe Ht Hcow
    have Hl0 : tv.length' = W64 0 := Hlen
    have Hl1 : tv.length' + W64 1 = W64 ↑1 := by rw [Hl0]; rfl
    have Hs1 : Sorted o.lt [(item, k)] := List.pairwise_singleton _ _
    iframe %Hdeg %Hl1 %Hs1
    isplitl []
    · unfold allItems
      imodintro
      iintro %e %he
      simp only [List.mem_singleton] at he
      subst he
      iexact Hitem
    iright
    iexists 0, Tree.node [(item, k)] []
    isplitr
    · ipureintro
      refine ⟨(shape_zero _ _ _).2 rfl, ⟨by simp; omega, by omega⟩, by simp⟩
    iapply ownNode_of_owned
    unfold ownedNode nodeShallow nodeFields
    iexists []
    simp only [Tree.items_node, Tree.children_node, List.map_cons, List.map_nil, ownNodes_nil]
    isplitl
    · iexists isl', csl
      iframe
      ipureintro; exact Hrn
    · itrivial
  · ihave %Hnn := ownNode_ne_null o _ _ _ _ _ _ $$ Hn
    wp_if_destruct
    · exact absurd Hif Hnn
    wp_apply wp_mutableFor o tv.cow' f less tv.root' tr $$ [Hn] as %r Hn
    · iframe Hn Hcow
    unfold ownedNode nodeShallow nodeFields
    icases Hn with ⟨%ps, ⟨%isl, %csl, ⟨%Hrn, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hns⟩
    wp_auto
    wp_apply wp_maxItems t (DFrac.own 1) ⟨tv.degree', tv.length', r, tv.cow'⟩ $$ [$Ht] as Ht
    have hmx : sint.Z (tv.degree' * W64 2 - W64 1) = 2 * (d : Int) - 1 := by word
    obtain ⟨is, cs⟩ := tr
    ihave %Hisl0 := ownSlice_len _ _ _ $$ Hisl
    simp only [List.length_map] at Hisl0
    have hrb1 : is.length ≤ 2 * d - 1 := Hrb.1
    have hisn : is.length = sint.nat isl.len := Hisl0.1
    have hisz : (sint.nat isl.len : Int) = sint.Z isl.len := by word
    wp_if_destruct
    · -- the root is full: split it
      have hisl : is.length = 2 * d - 1 := by omega
      ihave Hn : ownedNode o tv.cow' f less (DFrac.own 1) r (.node is cs) $$
          [Hi Hch Hw Hisl Hicap Hcsl Hccap Hns]
      · unfold ownedNode nodeShallow nodeFields
        iexists ps
        simp only [Tree.items_node, Tree.children_node]
        iframe Hns
        iexists isl, csl
        iframe
        ipureintro; exact Hrn
      wp_apply wp_maxItems t (DFrac.own 1) ⟨tv.degree', tv.length', r, tv.cow'⟩ $$ [$Ht] as Ht
      have hmw : sint.Z (BitVec.sdiv (tv.degree' * W64 2 - W64 1) (W64 2)) = (d : Int) - 1 := by
        word
      have hmwn : sint.nat (BitVec.sdiv (tv.degree' * W64 2 - W64 1) (W64 2)) = d - 1 := by
        word
      generalize BitVec.sdiv (tv.degree' * W64 2 - W64 1) (W64 2) = mw at *
      obtain ⟨e, he⟩ : ∃ e, is[sint.nat mw]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      dsimp only
      wp_apply wp_split o tv.cow' f less r is cs mw e (by omega) he (shape_children _ _ _ _ Hsh)
        $$ [Hn] as %n2 ⟨Hn, Hn2⟩
      · iframe Hn Hcow
      dsimp only
      wp_apply (wp_newNode (V := V) (K := K) (T := T) o tv.cow' f less) $$ [] as %nr Hnr
      · iexact Hcow
      unfold nodeShallow nodeFields
      icases Hnr with ⟨%nisl, %ncsl, ⟨%Hnrn, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
      wp_auto
      wp_apply wp_slice_literal (l := [e.1])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨Hz, -⟩
      wp_auto
      simp only [List.map_nil]
      wp_apply wp_slice_append $$ [$Hisl $Hicap $Hz] as %nisl' ⟨Hisl, Hicap, -⟩
      wp_apply wp_slice_literal (l := [r, n2])
      isplitr
      · ipureintro; rfl
      iintro %zsl2 ⟨Hz, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hz] as %ncsl' ⟨Hcsl, Hccap, -⟩
      dsimp only
      simp only [List.nil_append]
      ihave Hn := ownNode_of_owned o _ _ _ _ _ _ $$ Hn
      ihave Hn2 := ownNode_of_owned o _ _ _ _ _ _ $$ Hn2
      ihave Hn : ownedNode o tv.cow' f less (DFrac.own 1) nr
          (.node [e] [Tree.node (List.take (sint.nat mw) is) (List.take (sint.nat mw + 1) cs),
            Tree.node (List.drop (sint.nat mw + 1) is) (List.drop (sint.nat mw + 1) cs)]) $$
          [Hi Hch Hw Hisl Hicap Hcsl Hccap Hn Hn2]
      · unfold ownedNode nodeShallow nodeFields
        iexists [r, n2]
        simp only [Tree.items_node, Tree.children_node, ownNodes_cons, ownNodes_nil,
          List.map_cons, List.map_nil]
        iframe Hn Hn2
        iexists nisl', ncsl'
        iframe
        ipureintro; exact Hnrn
      have hcsh := shape_children _ _ _ _ Hsh
      obtain ⟨⟨hLs, hLl⟩, ⟨hRs, hRl⟩⟩ := shape_halves d h is cs (sint.nat mw) (by omega) hmwn hisl Hsh
      have tS0 : Tree.Shape d (h + 1) (.node [e]
          [Tree.node (List.take (sint.nat mw) is) (List.take (sint.nat mw + 1) cs),
            Tree.node (List.drop (sint.nat mw + 1) is) (List.drop (sint.nat mw + 1) cs)]) := by
        rw [shape_succ]
        refine ⟨rfl, fun c hc => ?_⟩
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨⟨by simp only [Tree.items_node]; omega, by simp only [Tree.items_node]; omega⟩, hLs⟩
        · exact ⟨⟨by simp only [Tree.items_node]; omega, by simp only [Tree.items_node]; omega⟩, hRs⟩
      have tE0 : (Tree.node [e]
          [Tree.node (List.take (sint.nat mw) is) (List.take (sint.nat mw + 1) cs),
            Tree.node (List.drop (sint.nat mw + 1) is) (List.drop (sint.nat mw + 1) cs)]).elems = s := by
        rw [← Hel, Tree.elems_node, Tree.elems_node, elemsAux_split (sint.nat mw) is cs e he hcsh]
        simp
      have tL0 : (Tree.node [e]
          [Tree.node (List.take (sint.nat mw) is) (List.take (sint.nat mw + 1) cs),
            Tree.node (List.drop (sint.nat mw + 1) is) (List.drop (sint.nat mw + 1) cs)]).items.length
          < 2 * d - 1 := by simp only [Tree.items_node, List.length_singleton]; omega
      have tRB0 : 0 < h + 1 → 1 ≤ (Tree.node [e]
          [Tree.node (List.take (sint.nat mw) is) (List.take (sint.nat mw + 1) cs),
            Tree.node (List.drop (sint.nat mw + 1) is) (List.drop (sint.nat mw + 1) cs)]).items.length :=
        fun _ => by simp
      clear Hsh Hrb Hel
      generalize nr = r0 at *
      generalize h + 1 = h0 at *
      generalize (Tree.node [e]
          [Tree.node (List.take (sint.nat mw) is) (List.take (sint.nat mw + 1) cs),
            Tree.node (List.drop (sint.nat mw + 1) is) (List.drop (sint.nat mw + 1) cs)]) = t0 at *
      roi_tail
    -- not full
    ihave Hn : ownedNode o tv.cow' f less (DFrac.own 1) r (.node is cs) $$
        [Hi Hch Hw Hisl Hicap Hcsl Hccap Hns]
    · unfold ownedNode nodeShallow nodeFields
      iexists ps
      simp only [Tree.items_node, Tree.children_node]
      iframe Hns
      iexists isl, csl
      iframe
      ipureintro; exact Hrn
    have tS0 := Hsh
    have tE0 := Hel
    have tL0 : (Tree.node is cs).items.length < 2 * d - 1 := by
      simp only [Tree.items_node]; omega
    have tRB0 := Hrb.2
    generalize r = r0 at *
    generalize h = h0 at *
    generalize Tree.node is cs = t0 at *
    roi_tail

end proof

end btree
end EtcdGrove
end Perennial
