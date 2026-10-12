module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__insert
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__find
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__insertAt
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__maybeSplitChild
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__mutableChild
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
/-- The common tail of `insert`: `return n.mutableChild(i).insert(item, maxItems)`, on the
node `.node isX csX` (the original one, or after splitting child `i`), whose contents are
the original's. -/
local macro "insert_tail" : tactic => `(tactic| (
  unfold ownedNode
  icases Hn with ⟨%psX, Hsh, Hns⟩
  simp only [Tree.items_node, Tree.children_node]
  ihave %HpsXl := ownNodes_length o c f less _ psX _ $$ Hns
  have hcXl := ((shape_succ _ _ _ _).1 tS).1
  obtain ⟨p, hp⟩ : ∃ p, psX[sint.nat jw]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by
      rcases List.getElem?_eq_some_iff.1 tC with ⟨h, _⟩; omega)⟩
  icases (ownNodes_extract o c f less _ psX _ _ p _ hp tC).1 $$ Hns with ⟨Hc', Hns⟩
  wp_apply wp_mutableChild o c f less n _ psX _ p _ tJ0 hp $$ [Hsh Hc']
    as %c' ⟨Hsh, Hc'⟩
  · iframe; iexact Hcow
  have ⟨tCb, tCs⟩ := shape_child _ _ _ _ _ _ tS tC
  have tSorted := tE ▸ hsorted
  obtain ⟨hcs, hmem, hlk, hins⟩ := descend_child o.order _ _ _ _ k hcXl tC tSorted tLo tHi
  wp_apply (IH h' (by omega) c' _ item k maxItems d tCs hcs tCl hmax hd2 hd62)
    $$ [Hc'] as %old %fnd ⟨%t'', Hc', % ⟨ht1, ht2, ht3, ht4, ht5, ht6⟩⟩
  · iframe Hc' Hcow Hitem
    iapply allItems_mono o _ _ (fun x hx => tE ▸ hmem x hx) $$ Hall
  ihave Hc' := ownNode_of_owned o c f less _ c' t'' $$ Hc'
  ihave Hns := ownNodes_fill o c f less _ psX _ (sint.nat jw) c' t''
    (by rcases List.getElem?_eq_some_iff.1 hp with ⟨h, _⟩; exact h) HpsXl $$ [Hc' Hns]
  · iframe
  iapply HΦ
  iexists Tree.node _ (List.set _ (sint.nat jw) t'')
  unfold nodeShallow nodeFields
  simp only [Tree.items_node, Tree.children_node, Tree.elems_node]
  icases Hsh with ⟨%isl', %csl', ⟨%Hnn', Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
  iframe
  ipureintro
  try simp only [Tree.items_node] at tCb ht3 ht4 tCl
  refine ⟨Hnn', shape_set_child _ _ _ _ _ _ tS ht1 ⟨by omega, by omega⟩, ?_, tL1, tL2, ?_, ?_⟩
  · rw [hins t'' item ht2, tE]
  · rw [← tE, hlk]; exact ht5
  · rw [← tE, hlk]; exact ht6))

theorem node.insert.wp_proof
    (wp_find : items.find.spec (GF := GF) (hG := hG))
    (wp_insertAt : items.insertAt.spec (GF := GF) (hG := hG))
    (wp_maybeSplitChild : node.maybeSplitChild.spec (GF := GF) (hG := hG))
    (wp_mutableChild : node.mutableChild.spec (GF := GF) (hG := hG)) :
    node.insert.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less
  suffices H : ∀ (h : Nat) (n : Loc) (t : Tree (V × K)) (item : V) (k : K) (maxItems : w64)
      (d : Nat), t.Shape d h → Sorted o.lt t.elems →
      t.items.length < 2 * d - 1 → sint.Z maxItems = 2 * (d : Int) - 1 → 2 ≤ d → d ≤ 2 ^ 62 →
      {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗
          ownedNode o c f less (DFrac.own 1) n t ∗ o.item item k ∗ allItems o t.elems }}
        (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"insert")) (Val #item))
          (Val #maxItems))
      {{ (old : V) (found : Bool), RET (PairV #old #found);
          ∃ t' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t' ∗
          ⌜t'.Shape d h ∧ t'.elems = insert o.lt t.elems (item, k) ∧
            t.items.length ≤ t'.items.length ∧ t'.items.length ≤ t.items.length + 1 ∧
            old = (lookup t.elems k).getD (zero_val V) ∧
            found = (lookup t.elems k).isSome⌝ }} by
    intro n t item k maxItems d h
    exact H h n t item k maxItems d
  intro h
  induction h using Nat.strongRecOn with
  | ind h IH =>
  intro n t item k maxItems d hshape hsorted hlen hmax hd2 hd62
  obtain ⟨is, cs⟩ := t
  simp only [Tree.items_node, Tree.elems_node] at hsorted hlen ⊢
  wp_start as ⟨#Hcow, Hn, #Hitem, #Hall⟩
  ihave ⟨#Hc, #Hfl, #Hless⟩ := (show isCow o c f less ⊢ iprop(c ↦□ (copyOnWriteContext.mk f less : copyOnWriteContext V) ∗
      isFreeList (V := V) f ∗ isLess o less) by unfold isCow; exact .rfl) $$ Hcow
  iStructNamed Hc
  unfold ownedNode nodeShallow nodeFields
  icases Hn with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hns⟩
  simp only [Tree.items_node, Tree.children_node]
  wp_alloc_anon
  wp_pures
  wp_alloc_anon
  wp_auto
  have hsis : Sorted o.lt is := sorted_sublist (items_sublist is cs) hsorted
  wp_apply wp_find o isl is (DFrac.own 1) item k less hsis $$ [$Hisl $Hless $Hitem]
    as %idx %found ⟨Hisl, %Hidx, %Hidx0, %Hfound⟩
  · iapply allItems_mono o is _ (fun x hx => (items_sublist is cs).subset hx) $$ Hall
  ihave %Hislen := ownSlice_len _ _ _ $$ Hisl
  simp only [List.length_map] at Hislen
  have hcnt := countLt_le (lt := o.lt) is k
  wp_if_destruct
  · -- not found
    have hnf : ∀ e, is[countLt o.lt is k]? = some e → e.2 ≠ k := by
      intro e he hek
      have := Hfound.2 ⟨e, Hidx ▸ he, hek⟩
      exact absurd this (by simp)
    have hlo := countLt_lo (lt := o.lt) is k
    have hhi := countLt_hi o.order is k hsis hnf
    rw [← Hidx] at hlo hhi
    ihave %Hcslen := ownSlice_len _ _ _ $$ Hcsl
    ihave %Hpslen := ownNodes_length o c f less _ ps cs $$ Hns
    wp_if_destruct
    · -- a leaf
      have hcs : cs = [] := by
        have h0 : ps.length = 0 := by rw [Hcslen.1, Hif]; rfl
        rw [← List.length_eq_zero_iff, ← Hpslen, h0]
      subst hcs
      wp_apply wp_insertAt (n.[node V, go!"items"]) isl (is.map Prod.fst) idx item Hidx0
        (by simp; word) $$ [$Hi $Hisl $Hicap] as %isl' ⟨Hi, Hisl, Hicap⟩
      obtain ⟨hlk, hins⟩ := leaf_insert o.order is (sint.nat idx) k hlo hhi
      iapply HΦ
      iexists Tree.node (is.take (sint.nat idx) ++ (item, k) :: is.drop (sint.nat idx)) []
      simp only [Tree.items_node, Tree.children_node, Tree.elems_node, Tree.elemsAux_nil,
        List.map_append, List.map_take, List.map_drop, List.map_cons]
      iframe
      ipureintro
      have hidxle : sint.nat idx ≤ is.length := by omega
      refine ⟨Hnn, ?_, hins item, by simp; omega, by simp; omega, by rw [hlk]; rfl,
        by rw [hlk]; rfl⟩
      cases h with
      | zero => exact (shape_zero _ _ _).2 rfl
      | succ h => exact absurd ((shape_succ _ _ _ _).1 hshape).1 (by simp)
    -- an internal node
    cases h with
    | zero =>
      exfalso; apply Hif
      have h0 := (shape_zero _ _ _).1 hshape
      rw [h0] at Hpslen
      have h1 : ps.length = 0 := by rw [Hpslen]; rfl
      have : sint.nat csl.len = 0 := by omega
      word
    | succ h' =>
    have hcl : cs.length = is.length + 1 := ((shape_succ _ _ _ _).1 hshape).1
    obtain ⟨ci, hci⟩ : ∃ ci, cs[sint.nat idx]? = some ci :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨cis, ccs⟩ := ci
    have ⟨hcib, hcis⟩ := shape_child _ _ _ _ _ _ hshape hci
    simp only [Tree.items_node] at hcib
    wp_apply wp_maybeSplitChild o c f less n is cs idx maxItems cis ccs Hidx0 (by omega) hci
      (shape_children _ _ _ _ hcis) (by omega) $$ [Hi Hch Hw Hisl Hicap Hcsl Hccap Hns]
      as %b Hb
    · isplitl []
      · iexact Hcow
      unfold ownedNode nodeShallow nodeFields
      iexists ps
      simp only [Tree.items_node, Tree.children_node]
      iframe Hns
      iexists isl, csl
      iframe
      ipureintro; exact Hnn
    by_cases hfull : cis.length < sint.nat maxItems
    · -- no split
      simp only [hfull, ↓reduceIte]
      icases Hb with ⟨%hb, Hn⟩
      subst hb
      wp_auto
      have tS := hshape
      have tE : Tree.elemsAux is cs = Tree.elemsAux is cs := rfl
      have tC := hci
      have tCl : (Tree.node cis ccs).items.length < 2 * d - 1 := by simp only [Tree.items_node]; word
      have tLo := hlo
      have tHi := hhi
      have tL1 : is.length ≤ is.length := Nat.le_refl _
      have tL2 : is.length ≤ is.length + 1 := Nat.le_succ _
      have tJ0 := Hidx0
      generalize idx = jw at *
      insert_tail
    -- child `idx` is full: split it, its middle item `e` moves up to `idx`
    simp only [hfull, ↓reduceIte]
    icases Hb with ⟨%hb, %e, %he, Hn⟩
    subst hb
    have hmaxn : sint.nat maxItems = 2 * d - 1 := by
      have : (sint.nat maxItems : Int) = sint.Z maxItems := by word
      omega
    have hm : sint.nat maxItems / 2 = d - 1 := by omega
    have hcisl : cis.length = 2 * d - 1 := by omega
    have hidxle : sint.nat idx ≤ is.length := by omega
    have hidxc : sint.nat idx < cs.length := by omega
    have tS := shape_splitChild d h' is cs (sint.nat idx) _ cis ccs e (by omega) hm hshape hci
      hcisl
    have tE := elemsAux_splitChild is cs (sint.nat idx) (sint.nat maxItems / 2) cis ccs e hcl hci
      he (shape_children _ _ _ _ hcis)
    have he2 : (is.take (sint.nat idx) ++ e :: is.drop (sint.nat idx))[sint.nat idx]? = some e := by
      rw [getElem?_insertAt _ _ _ _ hidxle]; simp
    have hemem : e ∈ Tree.elemsAux is cs := by
      rw [← tE]; exact (items_sublist _ _).subset (List.mem_of_getElem? he2)
    ihave #He := allItems_mem o _ e hemem $$ Hall
    unfold ownedNode nodeShallow nodeFields
    icases Hn with ⟨%ps2, ⟨%isl2, %csl2, ⟨%Hnn2, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hns⟩
    simp only [Tree.items_node, Tree.children_node]
    ihave %Hisl2 := ownSlice_len _ _ _ $$ Hisl
    simp only [List.length_map, List.length_append, List.length_take, List.length_cons,
      List.length_drop] at Hisl2
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index isl2 (sint.Z idx) _ _ e.1 (by word) $$ [Hisl] as Hisl
    · iframe; ipureintro
      rw [show (sint.Z idx).toNat = sint.nat idx from rfl, List.getElem?_map, he2]; rfl
    unfold isLess
    wp_apply Hless $$ %item %e.1 %k %e.2 [] as %r1 %Hr1
    · iframe Hitem He
    have hbL := split_bounds_left is (sint.nat idx) e k hidxle hlo hhi
    have hbR := split_bounds_right is (sint.nat idx) e k hidxle hlo hhi
    have hcL := getElem?_split_left cs (sint.nat idx)
      (Tree.node (List.take (sint.nat maxItems / 2) cis) (List.take (sint.nat maxItems / 2 + 1) ccs))
      (Tree.node (List.drop (sint.nat maxItems / 2 + 1) cis) (List.drop (sint.nat maxItems / 2 + 1) ccs))
      hidxc
    have hcR := getElem?_split_right cs (sint.nat idx)
      (Tree.node (List.take (sint.nat maxItems / 2) cis) (List.take (sint.nat maxItems / 2 + 1) ccs))
      (Tree.node (List.drop (sint.nat maxItems / 2 + 1) cis) (List.drop (sint.nat maxItems / 2 + 1) ccs))
      hidxc
    have hLl : (List.take (sint.nat maxItems / 2) cis).length < 2 * d - 1 := by simp; omega
    have hRl : (List.drop (sint.nat maxItems / 2 + 1) cis).length < 2 * d - 1 := by simp; omega
    have his2l : (is.take (sint.nat idx) ++ e :: is.drop (sint.nat idx)).length = is.length + 1 := by
      simp; omega
    have tSorted2 := tE ▸ hsorted
    have hfnd2 := found_item o.order _ _ (sint.nat idx) e e.2 he2 rfl tSorted2
    generalize (is.take (sint.nat idx) ++ e :: is.drop (sint.nat idx)) = is2 at *
    generalize (List.take (sint.nat idx) cs ++
        Tree.node (List.take (sint.nat maxItems / 2) cis) (List.take (sint.nat maxItems / 2 + 1) ccs) ::
          Tree.node (List.drop (sint.nat maxItems / 2 + 1) cis) (List.drop (sint.nat maxItems / 2 + 1) ccs) ::
            List.drop (sint.nat idx + 1) cs) = cs2 at *
    ihave Hn : ownedNode o c f less (DFrac.own 1) n (.node is2 cs2) $$
        [Hi Hch Hw Hisl Hicap Hcsl Hccap Hns]
    · unfold ownedNode nodeShallow nodeFields
      iexists ps2
      simp only [Tree.items_node, Tree.children_node]
      iframe Hns
      iexists isl2, csl2
      iframe
      ipureintro; exact Hnn2
    cases r1
    · -- not below `e`
      have hnk : ¬ o.lt k e.2 := fun h => absurd (Hr1.2 h) (by simp)
      unfold ownedNode nodeShallow nodeFields
      icases Hn with ⟨%ps2, ⟨%isl2, %csl2, ⟨%Hnn2, Hi, Hch, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hns⟩
      simp only [Tree.items_node, Tree.children_node]
      ihave %Hisl2' := ownSlice_len _ _ _ $$ Hisl
      simp only [List.length_map] at Hisl2'
      wp_auto
      wp_apply Hless $$ %e.1 %item %e.2 %k [] as %r2 %Hr2
      · iframe Hitem He
      cases r2
      · -- equal to `e`: replace it
        have hek : e.2 = k := by
          rcases o.order.total e.2 k with h | h | h
          · exact absurd (Hr2.2 h) (by simp)
          · exact h
          · exact absurd h hnk
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply wp_load_slice_index isl2 (sint.Z idx) _ _ e.1 (by word) $$ [Hisl] as Hisl
        · iframe; ipureintro
          rw [show (sint.Z idx).toNat = sint.nat idx from rfl, List.getElem?_map, he2]; rfl
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
        wp_apply wp_store_slice_index isl2 (sint.Z idx) _ item $$ [Hisl] as Hisl
        · iframe; ipureintro; simp only [List.length_map]; word
        wp_auto
        obtain ⟨hlk, hins⟩ := hfnd2
        rw [hek] at hlk hins
        iapply HΦ
        iexists Tree.node (is2.set (sint.nat idx) (item, k)) cs2
        iframe
        rw [show (sint.Z idx).toNat = sint.nat idx from rfl]
        simp only [Tree.items_node, Tree.children_node, Tree.elems_node, List.map_set]
        iframe
        ipureintro
        refine ⟨Hnn2, shape_set_items _ _ is2 _ cs2 List.length_set tS, ?_,
          by simp; omega, by simp; omega, ?_, ?_⟩
        · rw [hins item, tE]
        · rw [← tE, hlk]; rfl
        · rw [← tE, hlk]; rfl
      · -- above `e`: child `idx + 1`
        wp_auto
        ihave Hn : ownedNode o c f less (DFrac.own 1) n (.node is2 cs2) $$
            [Hi Hch Hw Hisl Hicap Hcsl Hccap Hns]
        · unfold ownedNode nodeShallow nodeFields
          iexists ps2
          simp only [Tree.items_node, Tree.children_node]
          iframe Hns
          iexists isl2, csl2
          iframe
          ipureintro; exact Hnn2
        have hidx1 : sint.nat (idx + W64 1) = sint.nat idx + 1 := by word
        obtain ⟨tLo, tHi⟩ := hbR (Hr2.1 rfl)
        rw [← hidx1] at tLo tHi hcR
        have tC := hcR
        have tCl := hRl
        have tL1 : is.length ≤ is2.length := by omega
        have tL2 : is2.length ≤ is.length + 1 := by omega
        have tJ0 : 0 ≤ sint.Z (idx + W64 1) := by word
        generalize idx + W64 1 = jw at *
        insert_tail
    · -- below `e`: child `idx`
      wp_auto
      obtain ⟨tLo, tHi⟩ := hbL (Hr1.1 rfl)
      have tC := hcL
      have tCl := hLl
      have tL1 : is.length ≤ is2.length := by omega
      have tL2 : is2.length ≤ is.length + 1 := by omega
      have tJ0 := Hidx0
      generalize idx = jw at *
      insert_tail
  -- found: replace item `idx`
  obtain ⟨x, hx, hxk⟩ := Hfound.1 rfl
  have hxlt : sint.nat idx < is.length := by
    rcases List.getElem?_eq_some_iff.1 hx with ⟨h, _⟩; exact h
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index isl (sint.Z idx) _ _ x.1 (by word) $$ [Hisl] as Hisl
  · iframe; ipureintro
    rw [show (sint.Z idx).toNat = sint.nat idx from rfl, List.getElem?_map, hx]; rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_store_slice_index isl (sint.Z idx) _ item $$ [Hisl] as Hisl
  · iframe; ipureintro; simp only [List.length_map]; word
  obtain ⟨hlk, hins⟩ := found_item o.order is cs (sint.nat idx) x k hx hxk hsorted
  wp_auto
  iapply HΦ
  iexists Tree.node (is.set (sint.nat idx) (item, k)) cs
  iframe
  rw [show (sint.Z idx).toNat = sint.nat idx from rfl]
  simp only [Tree.items_node, Tree.children_node, Tree.elems_node, List.map_set]
  iframe
  ipureintro
  refine ⟨Hnn, shape_set_items d h is _ cs List.length_set hshape, hins item,
    by simp, by simp, by rw [hlk]; rfl, by rw [hlk]; rfl⟩


end proof

end btree
end EtcdGrove
end Perennial
