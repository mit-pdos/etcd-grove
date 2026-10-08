import EtcdGrove.Btree.Spec.node__remove
import EtcdGrove.Btree.Spec.node__growChildAndRemove
import EtcdGrove.Btree.Spec.items__find
import EtcdGrove.Btree.Spec.items__removeAt
import EtcdGrove.Btree.Spec.items__pop
import EtcdGrove.Btree.Spec.items__insertAt
import EtcdGrove.Btree.Spec.node__mutableChild
import EtcdGrove.Btree.Spec.copyOnWriteContext__freeNode
import EtcdGrove.Btree.Lemmas.Remove

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree
open RemoveLemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

section loeb
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
  [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

/-- `node.remove.spec` for fixed items, order and context, as an Iris proposition. -/
def removeI : IProp GF :=
  iprop(∀ (n : Loc) (t : Tree (V × K)) (item : V) (tgt : Target K) (minItems typ : w64)
      (d h : Nat),
    ⌜t.Shape d h ∧ Sorted o.lt t.elems ∧ t.items.length ≤ 2 * d - 1 ∧
      sint.Z minItems = d - 1 ∧ 2 ≤ d ∧ d ≤ 2 ^ 62 ∧ typ = tgt.code ∧
      (h = 0 → tgt.code ≠ W64 0 → 1 ≤ t.items.length) ∧
      (0 < h → 1 ≤ t.items.length ∨ ∃ c0, t.children[0]? = some c0 ∧ d ≤ c0.items.length)⌝ →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less ∗
        ownedNode o c f less (DFrac.own 1) n t ∗ targetItem o tgt item ∗ allItems o t.elems }}
      (App (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"remove")) (Val #item))
        (Val #minItems)) (Val #typ))
    {{ (out : V) (found : Bool), RET (PairV #out #found);
        ∃ t' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t' ∗
        ⌜RemPost o.lt d h tgt t t' out found (zero_val V)⌝ }})

/-- `node.growChildAndRemove.spec` for fixed items, order and context. -/
def growI : IProp GF :=
  iprop(∀ (n : Loc) (t : Tree (V × K)) (item : V) (tgt : Target K) (i minItems typ : w64)
      (d h : Nat) (ci : Tree (V × K)),
    ⌜t.Shape d h ∧ 0 < h ∧ Sorted o.lt t.elems ∧ t.items.length ≤ 2 * d - 1 ∧
      1 ≤ t.items.length ∧ sint.Z minItems = d - 1 ∧ 2 ≤ d ∧ d ≤ 2 ^ 62 ∧ typ = tgt.code ∧
      0 ≤ sint.Z i ∧ sint.nat i = remIdx o.lt tgt t.items ∧
      t.children[sint.nat i]? = some ci ∧ ci.items.length ≤ d - 1⌝ →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less ∗
        ownedNode o c f less (DFrac.own 1) n t ∗ targetItem o tgt item ∗ allItems o t.elems }}
      (App (App (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"growChildAndRemove"))
        (Val #i)) (Val #item)) (Val #minItems)) (Val #typ))
    {{ (out : V) (found : Bool), RET (PairV #out #found);
        ∃ t' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t' ∗
        ⌜t'.Shape d h ∧ t'.elems = (removeOp tgt t.elems).1 ∧
          out = ((removeOp tgt t.elems).2).getD (zero_val V) ∧
          found = ((removeOp tgt t.elems).2).isSome ∧
          t'.items.length ≤ t.items.length ∧ t.items.length ≤ t'.items.length + 1⌝ }})

set_option maxHeartbeats 4000000 in
theorem remove_grow (wp_find : items.find.spec (GF := GF) (hG := hG))
    (wp_removeAt : items.removeAt.spec (GF := GF) (hG := hG))
    (wp_pop : items.pop.spec (GF := GF) (hG := hG))
    (wp_insertAt : items.insertAt.spec (GF := GF) (hG := hG))
    (wp_mutableChild : node.mutableChild.spec (GF := GF) (hG := hG))
    (wp_freeNode : copyOnWriteContext.freeNode.spec (GF := GF) (hG := hG)) :
    ⊢ removeI (T := T) o c f less ∧ growI (T := T) o c f less := by
  iloeb as IH
  isplit
  · unfold removeI growI
    iintro %n %t %item %tgt %minItems %typ %d %h %Hpre
    obtain ⟨Hshape, Hsorted, Hlen, Hmin, Hd2, Hd62, Htyp, Hleaf, Hint⟩ := Hpre
    wp_start as ⟨#Hcow, Hn, #Hitem, #Hall⟩
    wp_alloc_anon
    wp_pures
    wp_alloc_anon
    wp_auto
    cases t with
    | node is cs =>
    icases ownedNode_open o c f less _ n is cs $$ Hn with ⟨%ps, %isl, %csl, Hr⟩
    unfold ownedRes
    icases Hr with ⟨%Hnn, Hi, Hc, Hw, Hisl, Hicap, Hcsl, Hccap, Hch⟩
    ihave %Hpl := ownNodes_length o c f less _ _ _ $$ Hch
    ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
    ihave %Hil := ownSlice_len _ _ _ $$ Hisl
    cases h with
    | zero =>
      rw [shape_zero] at Hshape
      subst Hshape
      have hps : ps = [] := by simpa using Hpl
      subst hps
      have hc0 : csl.len = W64 0 := by simp only [List.length_nil] at Hcl; word
      simp only [Tree.items_node, Tree.elems_node, Tree.elemsAux_nil] at Hsorted Hlen Hleaf
      cases tgt with
      | max =>
        simp only [Target.code] at Htyp
        subst Htyp
        wp_auto
        rw [decide_eq_true hc0]
        wp_auto
        have h1 : 1 ≤ is.length := by simpa [Target.code] using Hleaf
        have hne : is ≠ [] := by intro h; subst h; simp at h1
        wp_apply wp_pop (structFieldRef (node V) go!"items" n) isl (is.map Prod.fst)
          ((is.getLast hne).1) (by rw [List.getLast?_map, List.getLast?_eq_some_getLast hne]; rfl)
          $$ [Hi Hisl Hicap] as %isl' ⟨Hi, Hisl, Hicap⟩
        · iframe
        iapply HΦ
        iexists (Tree.node is.dropLast [])
        isplitl
        · iapply ownedNode_close o c f less _ n is.dropLast [] [] isl' csl
          unfold ownedRes
          rw [List.map_dropLast]
          iframe
          ipureintro; exact Hnn
        · ipureintro; exact rem_leaf_max d is _ hne
      | min =>
        simp only [Target.code] at Htyp
        subst Htyp
        wp_auto
        rw [decide_eq_true hc0]
        wp_auto
        have h1 : 1 ≤ is.length := by simpa [Target.code] using Hleaf
        obtain ⟨x, hx⟩ : ∃ x, is[0]? = some x := ⟨is[0], List.getElem?_eq_getElem (by omega)⟩
        have hz0 : 0 ≤ sint.Z (W64 0) := by decide
        have hz1 : (is.map Prod.fst)[sint.nat (W64 0)]? = some x.1 := by
          rw [show sint.nat (W64 0) = 0 from rfl, List.getElem?_map, hx]; rfl
        wp_apply wp_removeAt (structFieldRef (node V) go!"items" n) isl (is.map Prod.fst) (W64 0)
          x.1 hz0 hz1
          $$ [Hi Hisl Hicap] as %isl' ⟨Hi, Hisl, Hicap⟩
        · iframe
        iapply HΦ
        iexists (Tree.node (is.drop 1) [])
        isplitl
        · iapply ownedNode_close o c f less _ n (is.drop 1) [] [] isl' csl
          unfold ownedRes
          simp only [List.take_zero, List.nil_append,
            List.map_drop]
          iframe
          ipureintro; exact Hnn
        · ipureintro; exact rem_leaf_min d is x _ hx
      | key k =>
        simp only [Target.code] at Htyp
        subst Htyp
        ihave #Hless := isCow_less_rm o f less c $$ Hcow
        ihave #HisLess := isCow_isLess_rm o f less c $$ Hcow
        ihave #Hall' := allItems_mono_rm o (l1 := is) (l2 := (Tree.node is []).elems)
          (fun e he => by simpa using he) $$ Hall
        rw [show targetItem o (Target.key k) item = o.item item k from rfl]
        wp_auto
        wp_method_call
        wp_call
        wp_auto
        wp_apply wp_find o isl is (DFrac.own 1) item k less Hsorted $$ [Hisl] as %idx %fnd ⟨Hisl, %Hres⟩
        · iframe # ∗
        obtain ⟨Hidx, Hidx0, Hfound⟩ := Hres
        rw [decide_eq_true hc0]
        wp_auto
        cases fnd with
        | false =>
          wp_auto
          iapply HΦ
          iexists (Tree.node is [])
          isplitl
          · iapply ownedNode_close o c f less _ n is [] [] isl csl
            unfold ownedRes
            iframe
            ipureintro; exact Hnn
          · ipureintro
            exact rem_leaf_key_notfound o.order d k is (sint.nat idx) _ Hsorted Hidx
              (fun hh => absurd (Hfound.2 hh) (by simp))
        | true =>
          obtain ⟨e, he, hek⟩ := Hfound.1 rfl
          wp_auto
          wp_apply wp_removeAt (structFieldRef (node V) go!"items" n) isl (is.map Prod.fst) idx
            e.1 Hidx0 (by rw [List.getElem?_map, he]; rfl)
            $$ [Hi Hisl Hicap] as %isl' ⟨Hi, Hisl, Hicap⟩
          · iframe
          iapply HΦ
          iexists (Tree.node (is.take (sint.nat idx) ++ is.drop (sint.nat idx + 1)) [])
          isplitl
          · iapply ownedNode_close o c f less _ n _ [] [] isl' csl
            unfold ownedRes
            simp only [List.map_append, List.map_take, List.map_drop]
            iframe
            ipureintro; exact Hnn
          · ipureintro
            exact rem_leaf_key_found o.order d k is _ e _ Hsorted he hek
    | succ h =>
      have hcl : cs.length = is.length + 1 := ((shape_succ d h is cs).1 Hshape).1
      have hcsl0 : csl.len ≠ W64 0 := by
        intro h0; rw [h0] at Hcl; have h00 : sint.nat (W64 0) = 0 := rfl; omega
      have hsi : Sorted o.lt is := sorted_sublist (items_sublist_elemsAux is cs)
        (by simpa using Hsorted)
      ihave #Hless := isCow_less_rm o f less c $$ Hcow
      ihave #HisLess := isCow_isLess_rm o f less c $$ Hcow
      ihave #Hall' := allItems_mono_rm o (l1 := is) (l2 := (Tree.node is cs).elems)
        (fun e he => (items_sublist_elemsAux is cs).subset (by simpa using he)) $$ Hall
      wp_join iprop(∃ (iv : w64) (fnd : Bool),
          i_ptr ↦ iv ∗ found_ptr ↦ fnd ∗ n_ptr ↦ n ∗ typ_ptr ↦ typ ∗ item_ptr ↦ item ∗
          structFieldRef (node V) go!"items" n ↦ isl ∗
          structFieldRef (node V) go!"children" n ↦ csl ∗
          structFieldRef (node V) go!"cow" n ↦ c ∗
          isl ↦* is.map Prod.fst ∗ csl ↦* ps ∗
          ⌜0 ≤ sint.Z iv ∧ sint.nat iv = remIdx o.lt tgt is ∧
            (fnd = true → ∃ k e, tgt = .key k ∧ is[sint.nat iv]? = some e ∧ e.2 = k) ∧
            (fnd = false → ∀ k, tgt = .key k → ¬ ∃ e, is[sint.nat iv]? = some e ∧ e.2 = k)⌝)
        at next with [i found n typ item Hi Hc Hw Hisl Hcsl]
        as ⟨%iv, %fnd, i, found, n, typ, item, Hi, Hc, Hw, Hisl, Hcsl, %Hiv⟩
      · cases tgt with
        | max =>
          simp only [Target.code] at Htyp
          subst Htyp
          wp_auto
          rw [decide_eq_false hcsl0]
          wp_auto
          wp_join_done
          iexists isl.len, false
          iframe
          ipureintro
          refine ⟨Hil.2, ?_, by simp, fun _ k hk => by cases hk⟩
          simp only [remIdx]; simp at Hil; omega
        | min =>
          simp only [Target.code] at Htyp
          subst Htyp
          wp_auto
          rw [decide_eq_false hcsl0]
          wp_auto
          wp_join_done
          iexists W64 0, false
          iframe
          ipureintro
          exact ⟨by decide, rfl, by simp, fun _ k hk => by cases hk⟩
        | key k =>
          simp only [Target.code] at Htyp
          subst Htyp
          rw [show targetItem o (Target.key k) item = o.item item k from rfl]
          wp_auto
          wp_method_call
          wp_call
          wp_auto
          wp_apply wp_find o isl is (DFrac.own 1) item k less hsi $$ [Hisl] as %idx %fnd ⟨Hisl, %Hres⟩
          · iframe # ∗
          obtain ⟨Hidx, Hidx0, Hfound⟩ := Hres
          rw [decide_eq_false hcsl0]
          wp_auto
          wp_join_done
          iexists idx, fnd
          iframe
          ipureintro
          refine ⟨Hidx0, Hidx, fun hf => ?_, fun hf k' hk => ?_⟩
          · obtain ⟨e, he, hek⟩ := Hfound.1 hf; exact ⟨k, e, rfl, he, hek⟩
          · cases hk; intro hh; have := Hfound.2 hh; simp [hf] at this
      obtain ⟨Hiv0, Hivr, Hft, Hff⟩ := Hiv
      have hjl : sint.nat iv ≤ is.length := Hivr ▸ remIdx_le o.lt tgt is
      have hjc : sint.nat iv < cs.length := by omega
      list_elem ps (sint.nat iv) as p
      list_elem cs (sint.nat iv) as ci
      have hb : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z csl.len := by word
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index csl (sint.Z iv) ps (DFrac.own 1) p Hiv0 $$ [Hcsl] as Hcsl
      · iframe; ipureintro; exact Hp_lookup
      icases (ownNodes_extract o c f less _ ps cs _ p ci Hp_lookup Hci_lookup).1 $$ Hch
        with ⟨Hp, Hch⟩
      icases ownNode_len_acc o c f less _ p ci $$ Hp with ⟨%cisl, %dq', Hpi, %Hcil, Hpclose⟩
      wp_auto
      ihave Hp := Hpclose $$ Hpi
      icases IH with ⟨#IHr, #IHg⟩
      have hcis := shape_child Hshape Hci_lookup
      wp_if_destruct
      · -- grow the child first
        have hcil : ci.items.length ≤ d - 1 := by word
        have h1 : 1 ≤ is.length := by
          rcases Hint (by omega) with h1 | ⟨c0, hc0, hd0⟩
          · simpa using h1
          · refine Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun hne => ?_)
            have his : is = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst his
            rw [remIdx_nil] at Hivr
            rw [Hivr] at Hci_lookup
            simp only [Tree.children_node] at hc0
            rw [hc0] at Hci_lookup; cases Hci_lookup; omega
        ihave Hch := (ownNodes_extract o c f less _ ps cs _ p ci Hp_lookup Hci_lookup).2 $$ [Hp Hch]
        · iframe
        ihave Hn := ownedNode_close o c f less _ n is cs ps isl csl $$ [Hi Hc Hw Hisl Hicap Hcsl Hccap Hch]
        · unfold ownedRes; iframe; ipureintro; exact Hnn
        wp_apply IHg $$ %n %(Tree.node is cs) %item %tgt %iv %minItems %typ %d %(h + 1) %ci
            [] [Hn]
          as %out %fnd' ⟨%t', Hn', %Hpost⟩
        · ipureintro
          exact ⟨Hshape, by omega, Hsorted, Hlen, by simpa using h1, Hmin, Hd2, Hd62, Htyp, Hiv0,
              by simpa using Hivr, by simpa using Hci_lookup, hcil⟩
        · iframe # ∗
        iapply HΦ
        iexists t'
        iframe
        ipureintro
        exact rem_grow d (h + 1) tgt (Tree.node is cs) t' out fnd' _ ci
          (by simpa [← Hivr] using Hci_lookup) hcil (by omega) Hpost
      · -- the child has enough items: descend
        have hdci : d ≤ ci.items.length := by word
        ihave Hsh : nodeShallow (V := V) c (DFrac.own 1) n is ps $$ [Hi Hc Hw Hisl Hicap Hcsl Hccap]
        · unfold nodeShallow nodeFields; iexists isl, csl; iframe; ipureintro; exact Hnn
        wp_apply wp_mutableChild o c f less n is ps iv p ci Hiv0 Hp_lookup $$ [Hsh Hp]
          as %c' ⟨Hsh, Hc'⟩
        · iframe # ∗
        unfold nodeShallow nodeFields
        icases Hsh with ⟨%isl2, %csl2, ⟨%_, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
        have hchsub := child_elems_sublist is cs _ ci Hci_lookup hjl
        have hcsorted : Sorted o.lt ci.elems := sorted_sublist hchsub (by simpa using Hsorted)
        ihave #Hallc := allItems_mono_rm o (l1 := ci.elems) (l2 := (Tree.node is cs).elems)
          (fun e he => by simpa using hchsub.subset he) $$ Hall
        have hpl' : sint.nat iv < ps.length := by omega
        cases fnd with
        | true =>
          obtain ⟨k, e, rfl, he, hek⟩ := Hft rfl
          have hjl' : sint.nat iv < is.length := (List.getElem?_eq_some_iff.1 he).1
          ihave %Hil2 := ownSlice_len _ _ _ $$ Hisl
          have hb2 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z isl2.len := by simp at Hil2; word
          wp_auto
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index isl2 (sint.Z iv) (is.map Prod.fst) (DFrac.own 1) e.1 Hiv0
            $$ [Hisl] as Hisl
          · iframe; ipureintro
            rw [show (sint.Z iv).toNat = sint.nat iv from rfl, List.getElem?_map, he]; rfl
          wp_apply IHr $$ %c' %ci %(zero_val V) %Target.max %minItems %(W64 2) %d %h [] [Hc']
            as %out' %fnd2 ⟨%ci', Hc', %Hpost⟩
          · ipureintro
            exact ⟨hcis.2, hcsorted, hcis.1.2, Hmin, Hd2, Hd62, rfl, fun _ _ => by omega,
              fun _ => .inl (by omega)⟩
          · iframe # ∗
            simp only [targetItem]
            itrivial
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index isl2 (sint.Z iv) (is.map Prod.fst) out' $$ [Hisl] as Hisl
          · iframe; ipureintro; exact ⟨Hiv0, by simp; word⟩
          obtain ⟨e', he', hpost⟩ := rem_pred o.order d h k is cs _ e ci ci' out' fnd2 _ Hshape
            (by simpa using Hsorted) he hek Hci_lookup hdci (by omega) Hpost
          iapply HΦ
          iexists (Tree.node (is.set (sint.nat iv) e') (cs.set (sint.nat iv) ci'))
          isplitl
          · iapply ownedNode_close o c f less _ n _ _ (ps.set (sint.nat iv) c') isl2 csl2
            unfold ownedRes
            rw [List.map_set, ← he']
            iframe
            isplitr
            · ipureintro; exact Hnn
            iapply ownNodes_fill o c f less _ ps cs _ c' ci' hpl' Hpl $$ [Hc' Hch]
            iframe
            iapply ownNode_of_owned
            iexact Hc'
          · ipureintro; exact hpost
        | false =>
          have hnf := Hff rfl
          wp_auto
          wp_apply IHr $$ %c' %ci %item %tgt %minItems %typ %d %h [] [Hc']
            as %out' %fnd2 ⟨%ci', Hc', %Hpost⟩
          · ipureintro
            exact ⟨hcis.2, hcsorted, hcis.1.2, Hmin, Hd2, Hd62, Htyp, fun _ _ => by omega,
              fun _ => .inl (by omega)⟩
          · iframe # ∗
          iapply HΦ
          iexists (Tree.node is (cs.set (sint.nat iv) ci'))
          isplitl
          · iapply ownedNode_close o c f less _ n _ _ (ps.set (sint.nat iv) c') isl2 csl2
            unfold ownedRes
            iframe
            isplitr
            · ipureintro; exact Hnn
            iapply ownNodes_fill o c f less _ ps cs _ c' ci' hpl' Hpl $$ [Hc' Hch]
            iframe
            iapply ownNode_of_owned
            iexact Hc'
          · ipureintro
            exact rem_desc o.order d h tgt is cs _ ci ci' out' fnd2 _ Hshape (by simpa using Hsorted)
              Hivr Hci_lookup hdci (by omega) hnf Hpost
  · unfold removeI growI
    iintro %n %t %item %tgt %i %minItems %typ %d %h %ci %Hpre
    obtain ⟨Hshape, Hh, Hsorted, Hlen, H1, Hmin, Hd2, Hd62, Htyp, Hi0, Hir, Hci, Hcil⟩ := Hpre
    wp_start as ⟨#Hcow, Hn, #Hitem, #Hall⟩
    icases IH with ⟨#IHr, #IHg⟩
    cases t with
    | node is cs =>
    obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    icases ownedNode_open o c f less _ n is cs $$ Hn with ⟨%ps, %isl, %csl, Hr⟩
    unfold ownedRes
    icases Hr with ⟨%Hnn, Hi, Hc, Hw, Hisl, Hicap, Hcsl, Hccap, Hch⟩
    ihave %Hpl := ownNodes_length o c f less _ _ _ $$ Hch
    ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
    ihave %Hil := ownSlice_len _ _ _ $$ Hisl
    simp only [Tree.items_node, Tree.children_node] at Hlen H1 Hir Hci
    have hcl : cs.length = is.length + 1 := ((shape_succ d h is cs).1 Hshape).1
    have hsorted : Sorted o.lt (Tree.elemsAux is cs) := by simpa using Hsorted
    have hsi : Sorted o.lt is := sorted_sublist (items_sublist_elemsAux is cs) hsorted
    have hjl : sint.nat i ≤ is.length := Hir ▸ remIdx_le o.lt tgt is
    wp_auto
    wp_join iprop(∃ t'' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t'' ∗
        n_ptr ↦ n ∗ typ_ptr ↦ typ ∗ minItems_ptr ↦ minItems ∗ item_ptr ↦ item ∗
        ⌜GrowMid o.lt d (h + 1) tgt (Tree.node is cs) t''⌝)
      at next with [-HΦ] as ⟨%t'', Hn, n, typ, minItems, item, %Hmid⟩
    · wp_join (Q := fun v => iprop(∃ b : Bool,
          ⌜v = #b ∧ (b = true ↔ (0 < sint.Z i ∧
            ∃ cl, cs[sint.nat i - 1]? = some cl ∧ d ≤ cl.items.length))⌝ ∗
          i_ptr ↦ i ∗ n_ptr ↦ n ∗ minItems_ptr ↦ minItems ∗
          structFieldRef (node V) go!"children" n ↦ csl ∗ csl ↦* ps ∗
          ownNodes o c f less (DFrac.own 1) ps cs))
        at (if: _ then _ else #false) with [i n minItems Hc Hcsl Hch]
        as ⟨%b, %Hb, i, n, minItems, Hc, Hcsl, Hch⟩
      · wp_if_destruct
        · have hj : sint.nat (i - W64 1) = sint.nat i - 1 := by word
          have hjc : sint.nat i - 1 < cs.length := by omega
          list_elem ps (sint.nat i - 1) as pl
          list_elem cs (sint.nat i - 1) as cl
          have hb : 0 ≤ sint.Z (i - W64 1) ∧ sint.Z (i - W64 1) < sint.Z csl.len := by word
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index csl (sint.Z (i - W64 1)) ps _ pl hb.1 $$ [Hcsl] as Hcsl
          · iframe; ipureintro
            rw [show (sint.Z (i - W64 1)).toNat = sint.nat i - 1 by word]; exact Hpl_lookup
          icases (ownNodes_extract o c f less _ ps cs _ pl cl Hpl_lookup Hcl_lookup).1 $$ Hch
            with ⟨Hp, Hch⟩
          icases ownNode_len_acc o c f less _ pl cl $$ Hp with ⟨%lisl, %dq', Hpi, %Hlil, Hpclose⟩
          wp_auto
          ihave Hp := Hpclose $$ Hpi
          ihave Hch := (ownNodes_extract o c f less _ ps cs _ pl cl Hpl_lookup Hcl_lookup).2
            $$ [Hp Hch]
          · iframe
          iexists _
          iframe
          ipureintro
          refine ⟨rfl, ?_⟩
          rw [decide_eq_true_iff]
          constructor
          · intro hlt; exact ⟨by word, cl, Hcl_lookup, by word⟩
          · rintro ⟨_, cl', hcl', hd'⟩; rw [Hcl_lookup] at hcl'; cases hcl'; word
        · iexists false
          iframe
          ipureintro
          refine ⟨rfl, ?_⟩
          simp only [Bool.false_eq_true, false_iff, not_and]
          intro h0; exact absurd h0 (by word)
      obtain ⟨rfl, Hb⟩ := Hb
      cases b with
      | true =>
        -- steal from the left sibling
        obtain ⟨hi0, cl, hclk, hdcl⟩ := Hb.1 rfl
        clear Hb
        have hi1 : 1 ≤ sint.nat i := by word
        wp_auto
        obtain ⟨Pc, a, b, Qc, hcs, hPc⟩ := rm_split2 cs (sint.nat i - 1) (by omega)
        obtain ⟨Pp, pa, pb, Qp, hps, hPp⟩ := rm_split2 ps (sint.nat i - 1) (by omega)
        obtain ⟨P, x, Q, his, hP⟩ := rm_split1 is (sint.nat i - 1) (by omega)
        subst hcs hps his
        have hiP : sint.nat i = P.length + 1 := by omega
        have hacl : a = cl := by
          rw [← hPc] at hclk; simp at hclk; exact hclk
        have hbci : b = ci := by
          rw [show sint.nat i = Pc.length + 1 by omega] at Hci; simp at Hci; exact Hci
        subst hacl hbci
        have hsa := shape_child (c := a) Hshape (j := Pc.length) (by simp)
        have hsb := shape_child (c := b) Hshape (j := Pc.length + 1) (by simp)
        icases (ownNodes_split2 o c f less _ Pp Qp Pc Qc pa pb a b (by omega)).1 $$ Hch
          with ⟨HP, Ha, Hb, HQ⟩
        ihave Hsh : nodeShallow (V := V) c (DFrac.own 1) n (P ++ x :: Q) (Pp ++ pa :: pb :: Qp)
          $$ [Hi Hc Hw Hisl Hicap Hcsl Hccap]
        · unfold nodeShallow nodeFields; iexists isl, csl; iframe; ipureintro; exact Hnn
        have hpb : (Pp ++ pa :: pb :: Qp)[sint.nat i]? = some pb := by
          rw [show sint.nat i = Pp.length + 1 by omega]; simp
        wp_apply wp_mutableChild o c f less n _ _ i pb b Hi0 hpb
          $$ [Hsh Hb] as %c1 ⟨Hsh, Hc1⟩
        · iframe # ∗
        rw [show sint.nat i = Pp.length + 1 by omega, set_mid1]
        have hpa : (Pp ++ pa :: c1 :: Qp)[sint.nat (i - W64 1)]? = some pa := by
          rw [show sint.nat (i - W64 1) = Pp.length by word]; simp
        wp_apply wp_mutableChild o c f less n _ _ (i - W64 1) pa a (by word) hpa
          $$ [Hsh Ha] as %c2 ⟨Hsh, Hc2⟩
        · iframe # ∗
        rw [show sint.nat (i - W64 1) = Pp.length by word, set_mid0]
        unfold nodeShallow nodeFields
        icases Hsh with ⟨%isl', %csl', ⟨%_, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
        cases a with
        | node Ais Acs =>
        cases b with
        | node Bis Bcs =>
        simp only [Tree.items_node] at hdcl Hcil hsa hsb
        rcases List.eq_nil_or_concat Ais with h0 | ⟨Ais', w, hA⟩
        · subst h0; simp at hdcl; omega
        rw [List.concat_eq_append] at hA; subst hA
        icases ownedNode_open o c f less _ c2 _ _ $$ Hc2 with ⟨%Lps, %lisl, %lcsl, Hr2⟩
        unfold ownedRes
        icases Hr2 with ⟨%Hnn2, Hi2, Hc2, Hw2, Hisl2, Hicap2, Hcsl2, Hccap2, Hch2⟩
        icases ownedNode_open o c f less _ c1 _ _ $$ Hc1 with ⟨%Cps, %cisl, %ccsl, Hr1⟩
        unfold ownedRes
        icases Hr1 with ⟨%Hnn1, Hi1, Hc1, Hw1, Hisl1, Hicap1, Hcsl1, Hccap1, Hch1⟩
        ihave %Hil' := ownSlice_len _ _ _ $$ Hisl
        simp only [List.map_append, List.map_cons, List.length_append, List.length_cons,
          List.length_map] at Hil'
        wp_apply wp_pop (structFieldRef (node V) go!"items" c2) lisl ((Ais' ++ [w]).map Prod.fst)
          w.1 (by simp) $$ [Hi2 Hisl2 Hicap2] as %lisl' ⟨Hi2, Hisl2, Hicap2⟩
        · iframe
        have hz : sint.Z (i - W64 1) = (P.length : Int) := by word
        have hz' : sint.Z isl'.len = (P.length + (Q.length + 1) : Nat) := by
          have := Hil'.1; have := Hil'.2; word
        have hb2 : 0 ≤ sint.Z (i - W64 1) ∧ sint.Z (i - W64 1) < sint.Z isl'.len := by
          rw [hz, hz']; omega
        simp only [hb2, _root_.and_self, ↓reduceIte]
        have hxi : ((P ++ x :: Q).map Prod.fst)[(sint.Z (i - W64 1)).toNat]? = some x.1 := by
          rw [show (sint.Z (i - W64 1)).toNat = P.length by word]; simp
        wp_apply wp_load_slice_index isl' (sint.Z (i - W64 1)) ((P ++ x :: Q).map Prod.fst) _ x.1
          hb2.1 $$ [Hisl] as Hisl
        · iframe; ipureintro; exact hxi
        wp_apply wp_insertAt (structFieldRef (node V) go!"items" c1) cisl (Bis.map Prod.fst) (W64 0)
          x.1 (by decide) (by simp) $$ [Hi1 Hisl1 Hicap1] as %cisl' ⟨Hi1, Hisl1, Hicap1⟩
        · iframe
        simp only [hb2, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index isl' (sint.Z (i - W64 1)) ((P ++ x :: Q).map Prod.fst) w.1
          $$ [Hisl] as Hisl
        · iframe; ipureintro; exact ⟨hb2.1, by rw [hz]; simp; omega⟩
        ihave %Hlps := ownNodes_length o c f less _ _ _ $$ Hch2
        ihave %Hlcl := ownSlice_len _ _ _ $$ Hcsl2
        wp_join iprop(∃ (Lps2 Cps2 : List Loc) (lcsl2 ccsl2 : GoSlice),
            structFieldRef (node V) go!"children" c2 ↦ lcsl2 ∗ lcsl2 ↦* Lps2 ∗
            ownSliceCap Loc lcsl2 (DFrac.own 1) ∗
            ownNodes o c f less (DFrac.own 1) Lps2 Acs.dropLast ∗
            structFieldRef (node V) go!"children" c1 ↦ ccsl2 ∗ ccsl2 ↦* Cps2 ∗
            ownSliceCap Loc ccsl2 (DFrac.own 1) ∗
            ownNodes o c f less (DFrac.own 1) Cps2 (Acs.getLast?.toList ++ Bcs))
          with [Hc2 Hcsl2 Hccap2 Hch2 Hc1 Hcsl1 Hccap1 Hch1 stealFrom child]
          as ⟨%Lps2, %Cps2, %lcsl2, %ccsl2, Hc2, Hcsl2, Hccap2, Hch2, Hc1, Hcsl1, Hccap1, Hch1⟩
        · -- internal children: move the last child too
          rcases List.eq_nil_or_concat Lps with h0 | ⟨Lps', lp, hL⟩
          · subst h0; exfalso; simp at Hlcl; word
          rw [List.concat_eq_append] at hL; subst hL
          rcases List.eq_nil_or_concat Acs with h0 | ⟨Acs', lc, hA⟩
          · subst h0; simp at Hlps
          rw [List.concat_eq_append] at hA; subst hA
          icases (ownNodes_app o c f less _ Lps' [lp] Acs' [lc] (by simpa using Hlps)).1 $$ Hch2
            with ⟨Hch2, Hlast⟩
          rw [ownNodes_cons, ownNodes_nil]
          icases Hlast with ⟨Hlast, -⟩
          wp_apply wp_pop (structFieldRef (node V) go!"children" c2) lcsl (Lps' ++ [lp]) lp
            (by simp) $$ [Hc2 Hcsl2 Hccap2] as %lcsl' ⟨Hc2, Hcsl2, Hccap2⟩
          · iframe
          wp_apply wp_insertAt (structFieldRef (node V) go!"children" c1) ccsl Cps (W64 0) lp
            (by decide) (by simp) $$ [Hc1 Hcsl1 Hccap1] as %ccsl' ⟨Hc1, Hcsl1, Hccap1⟩
          · iframe
          wp_join_done
          iexists Lps', lp :: Cps, lcsl', ccsl'
          have e1 : (Lps' ++ [lp]).dropLast = Lps' := by simp
          have e2 : (Acs' ++ [lc]).dropLast = Acs' := by simp
          have e3 : (Acs' ++ [lc]).getLast?.toList ++ Bcs = lc :: Bcs := by simp
          rw [e1, e2, e3]
          simp only [List.take_zero, List.drop_zero,
            List.nil_append]
          iframe
          rw [ownNodes_cons]
          iframe
        · -- leaves
          have h0 : Lps = [] := by
            apply List.eq_nil_of_length_eq_zero; rw [Hlcl.1]; word
          subst h0
          have h0 : Acs = [] := by simpa using Hlps.symm
          subst h0
          iexists [], Cps, lcsl, ccsl
          simp only [List.dropLast_nil, List.getLast?_nil, Option.toList_none, List.nil_append]
          iframe
        wp_join_done
        have hsl := steal_left (d := d) (h := h) Ais' Bis Acs Bcs w x Hd2 hsa hsb hdcl Hcil
        have hset : ((P ++ x :: Q).map Prod.fst).set (sint.Z (i - W64 1)).toNat w.1 =
            (P ++ w :: Q).map Prod.fst := by
          rw [show (sint.Z (i - W64 1)).toNat = P.length by word,
            show w.1 = Prod.fst w from rfl, ← List.map_set, set_mid]
        iexists (Tree.node (P ++ w :: Q) (Pc ++ Tree.node Ais' Acs.dropLast ::
          Tree.node (x :: Bis) (Acs.getLast?.toList ++ Bcs) :: Qc))
        iframe n typ minItems item
        isplitl
        · iapply ownedNode_close o c f less _ n _ _ (Pp ++ c2 :: c1 :: Qp) isl' csl'
          unfold ownedRes
          rw [hset]
          iframe
          isplitr
          · ipureintro; exact Hnn
          iapply (ownNodes_split2 o c f less _ Pp Qp Pc Qc c2 c1 _ _ (by omega)).2
          iframe
          isplitl [Hi2 Hc2 Hw2 Hisl2 Hicap2 Hcsl2 Hccap2 Hch2]
          · iapply ownNode_of_owned
            iapply ownedNode_close o c f less _ c2 _ _ Lps2 lisl' lcsl2
            unfold ownedRes
            rw [show ((Ais' ++ [w]).map Prod.fst).dropLast = Ais'.map Prod.fst by simp]
            iframe
            ipureintro; exact Hnn2
          · iapply ownNode_of_owned
            iapply ownedNode_close o c f less _ c1 _ _ Cps2 cisl' ccsl2
            unfold ownedRes
            rw [show (Bis.map Prod.fst).take 0 ++
                x.1 :: (Bis.map Prod.fst).drop 0 = (x :: Bis).map Prod.fst by simp]
            iframe
            ipureintro; exact Hnn1
        · ipureintro
          exact grow_window tgt P Q Pc Qc x w _ _ _ _ (by omega) Hshape Hlen hsl.1 hsl.2.1 hsl.2.2
      | false =>
        have hnL : ¬ (0 < sint.Z i ∧ ∃ cl, cs[sint.nat i - 1]? = some cl ∧ d ≤ cl.items.length) :=
          fun hh => by simpa using Hb.2 hh
        clear Hb
        wp_auto
        wp_join (Q := fun v => iprop(∃ b : Bool,
            ⌜v = #b ∧ (b = true ↔ (sint.nat i < is.length ∧
              ∃ cr, cs[sint.nat i + 1]? = some cr ∧ d ≤ cr.items.length))⌝ ∗
            i_ptr ↦ i ∗ n_ptr ↦ n ∗ minItems_ptr ↦ minItems ∗
            structFieldRef (node V) go!"items" n ↦ isl ∗
            structFieldRef (node V) go!"children" n ↦ csl ∗ csl ↦* ps ∗
            ownNodes o c f less (DFrac.own 1) ps cs))
          at (if: _ then _ else #false) with [i n minItems Hi Hc Hcsl Hch]
          as ⟨%b, %Hb, i, n, minItems, Hi, Hc, Hcsl, Hch⟩
        · wp_if_destruct
          · have hil : sint.nat i < is.length := by
              simp at Hil; word
            have hj : sint.nat (i + W64 1) = sint.nat i + 1 := by word
            have hjc : sint.nat i + 1 < cs.length := by omega
            list_elem ps (sint.nat i + 1) as pr
            list_elem cs (sint.nat i + 1) as cr
            have hb : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) < sint.Z csl.len := by word
            simp only [hb, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index csl (sint.Z (i + W64 1)) ps _ pr hb.1 $$ [Hcsl] as Hcsl
            · iframe; ipureintro
              rw [show (sint.Z (i + W64 1)).toNat = sint.nat i + 1 by word]; exact Hpr_lookup
            icases (ownNodes_extract o c f less _ ps cs _ pr cr Hpr_lookup Hcr_lookup).1 $$ Hch
              with ⟨Hp, Hch⟩
            icases ownNode_len_acc o c f less _ pr cr $$ Hp with ⟨%risl, %dq', Hpi, %Hril, Hpclose⟩
            wp_auto
            ihave Hp := Hpclose $$ Hpi
            ihave Hch := (ownNodes_extract o c f less _ ps cs _ pr cr Hpr_lookup Hcr_lookup).2
              $$ [Hp Hch]
            · iframe
            iexists _
            iframe
            ipureintro
            refine ⟨rfl, ?_⟩
            rw [decide_eq_true_iff]
            constructor
            · intro hlt; exact ⟨hil, cr, Hcr_lookup, by word⟩
            · rintro ⟨_, cr', hcr', hd'⟩; rw [Hcr_lookup] at hcr'; cases hcr'; word
          · iexists false
            iframe
            ipureintro
            refine ⟨rfl, ?_⟩
            simp only [Bool.false_eq_true, false_iff, not_and]
            intro h0; exact absurd h0 (by simp at Hil; word)
        obtain ⟨rfl, Hb⟩ := Hb
        cases b with
        | true =>
          -- steal from the right sibling
          obtain ⟨hil, cr, hcrk, hdcr⟩ := Hb.1 rfl
          clear Hb
          wp_auto
          obtain ⟨Pc, a, b, Qc, hcs, hPc⟩ := rm_split2 cs (sint.nat i) (by omega)
          obtain ⟨Pp, pa, pb, Qp, hps, hPp⟩ := rm_split2 ps (sint.nat i) (by omega)
          obtain ⟨P, x, Q, his, hP⟩ := rm_split1 is (sint.nat i) hil
          subst hcs hps his
          have hbcr : b = cr := by
            rw [← hPc] at hcrk; simp at hcrk; exact hcrk
          have haci : a = ci := by
            rw [← hPc] at Hci; simp at Hci; exact Hci
          subst hbcr haci
          have hsa := shape_child (c := a) Hshape (j := Pc.length) (by simp)
          have hsb := shape_child (c := b) Hshape (j := Pc.length + 1) (by simp)
          icases (ownNodes_split2 o c f less _ Pp Qp Pc Qc pa pb a b (by omega)).1 $$ Hch
            with ⟨HP, Ha, Hb, HQ⟩
          ihave Hsh : nodeShallow (V := V) c (DFrac.own 1) n (P ++ x :: Q) (Pp ++ pa :: pb :: Qp)
            $$ [Hi Hc Hw Hisl Hicap Hcsl Hccap]
          · unfold nodeShallow nodeFields; iexists isl, csl; iframe; ipureintro; exact Hnn
          have hpa : (Pp ++ pa :: pb :: Qp)[sint.nat i]? = some pa := by
            rw [show sint.nat i = Pp.length by omega]; simp
          wp_apply wp_mutableChild o c f less n _ _ i pa a Hi0 hpa $$ [Hsh Ha] as %c1 ⟨Hsh, Hc1⟩
          · iframe # ∗
          rw [show sint.nat i = Pp.length by omega, set_mid0]
          have hpb : (Pp ++ c1 :: pb :: Qp)[sint.nat (i + W64 1)]? = some pb := by
            rw [show sint.nat (i + W64 1) = Pp.length + 1 by word]; simp
          wp_apply wp_mutableChild o c f less n _ _ (i + W64 1) pb b (by word) hpb
            $$ [Hsh Hb] as %c2 ⟨Hsh, Hc2⟩
          · iframe # ∗
          rw [show sint.nat (i + W64 1) = Pp.length + 1 by word, set_mid1]
          unfold nodeShallow nodeFields
          icases Hsh with ⟨%isl', %csl', ⟨%_, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
          cases a with
          | node Ais Acs =>
          cases b with
          | node Bis Bcs =>
          simp only [Tree.items_node] at hdcr Hcil hsa hsb
          obtain ⟨w, Bis', rfl⟩ : ∃ w Bis', Bis = w :: Bis' := by
            cases Bis with
            | nil => simp at hdcr; omega
            | cons w Bis' => exact ⟨w, Bis', rfl⟩
          icases ownedNode_open o c f less _ c2 _ _ $$ Hc2 with ⟨%Bps, %bisl, %bcsl, Hr2⟩
          unfold ownedRes
          icases Hr2 with ⟨%Hnn2, Hi2, Hc2, Hw2, Hisl2, Hicap2, Hcsl2, Hccap2, Hch2⟩
          icases ownedNode_open o c f less _ c1 _ _ $$ Hc1 with ⟨%Aps, %aisl, %acsl, Hr1⟩
          unfold ownedRes
          icases Hr1 with ⟨%Hnn1, Hi1, Hc1, Hw1, Hisl1, Hicap1, Hcsl1, Hccap1, Hch1⟩
          ihave %Hil' := ownSlice_len _ _ _ $$ Hisl
          simp only [List.map_append, List.map_cons, List.length_append, List.length_cons,
            List.length_map] at Hil'
          have hz : sint.Z i = (P.length : Int) := by word
          have hz' : sint.Z isl'.len = (P.length + (Q.length + 1) : Nat) := by
            have := Hil'.1; have := Hil'.2; word
          have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z isl'.len := by rw [hz, hz']; omega
          have hw0 : ((w :: Bis').map Prod.fst)[sint.nat (W64 0)]? = some w.1 := by
            rw [show sint.nat (W64 0) = 0 from rfl]; simp
          wp_apply wp_removeAt (structFieldRef (node V) go!"items" c2) bisl
            ((w :: Bis').map Prod.fst) (W64 0) w.1 (by decide) hw0
            $$ [Hi2 Hisl2 Hicap2] as %bisl' ⟨Hi2, Hisl2, Hicap2⟩
          · iframe
          simp only [hb2, _root_.and_self, ↓reduceIte]
          have hxi : ((P ++ x :: Q).map Prod.fst)[(sint.Z i).toNat]? = some x.1 := by
            rw [show (sint.Z i).toNat = P.length by word]; simp
          wp_apply wp_load_slice_index isl' (sint.Z i) ((P ++ x :: Q).map Prod.fst) _ x.1
            hb2.1 $$ [Hisl] as Hisl
          · iframe; ipureintro; exact hxi
          wp_apply wp_slice_literal (l := [x.1])
          isplitr
          · ipureintro; rfl
          iintro %zsl ⟨Hz, -⟩
          wp_auto
          wp_apply wp_slice_append $$ [$Hisl1 $Hicap1 $Hz] as %aisl' ⟨Hisl1, Hicap1, -⟩
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index isl' (sint.Z i) ((P ++ x :: Q).map Prod.fst) w.1
            $$ [Hisl] as Hisl
          · iframe; ipureintro; exact ⟨hb2.1, by rw [hz]; simp; omega⟩
          ihave %Hbps := ownNodes_length o c f less _ _ _ $$ Hch2
          ihave %Hapsl := ownNodes_length o c f less _ _ _ $$ Hch1
          ihave %Hbcl := ownSlice_len _ _ _ $$ Hcsl2
          wp_join iprop(∃ (Aps2 Bps2 : List Loc) (acsl2 bcsl2 : GoSlice),
              structFieldRef (node V) go!"children" c1 ↦ acsl2 ∗ acsl2 ↦* Aps2 ∗
              ownSliceCap Loc acsl2 (DFrac.own 1) ∗
              ownNodes o c f less (DFrac.own 1) Aps2 (Acs ++ Bcs.take 1) ∗
              structFieldRef (node V) go!"children" c2 ↦ bcsl2 ∗ bcsl2 ↦* Bps2 ∗
              ownSliceCap Loc bcsl2 (DFrac.own 1) ∗
              ownNodes o c f less (DFrac.own 1) Bps2 (Bcs.drop 1))
            with [Hc2 Hcsl2 Hccap2 Hch2 Hc1 Hcsl1 Hccap1 Hch1 stealFrom child]
            as ⟨%Aps2, %Bps2, %acsl2, %bcsl2, Hc1, Hcsl1, Hccap1, Hch1, Hc2, Hcsl2, Hccap2, Hch2⟩
          · -- internal children: move the first child too
            obtain ⟨bp, Bps', rfl⟩ : ∃ bp Bps', Bps = bp :: Bps' := by
              cases Bps with
              | nil => exfalso; simp at Hbcl; word
              | cons bp Bps' => exact ⟨bp, Bps', rfl⟩
            obtain ⟨y, Bcs', rfl⟩ : ∃ y Bcs', Bcs = y :: Bcs' := by
              cases Bcs with
              | nil => simp at Hbps
              | cons y Bcs' => exact ⟨y, Bcs', rfl⟩
            rw [ownNodes_cons]
            icases Hch2 with ⟨Hfirst, Hch2⟩
            have hb0 : (bp :: Bps')[sint.nat (W64 0)]? = some bp := by
              rw [show sint.nat (W64 0) = 0 from rfl]; simp
            wp_apply wp_removeAt (structFieldRef (node V) go!"children" c2) bcsl (bp :: Bps')
              (W64 0) bp (by decide) hb0 $$ [Hc2 Hcsl2 Hccap2] as %bcsl' ⟨Hc2, Hcsl2, Hccap2⟩
            · iframe
            wp_apply wp_slice_literal (l := [bp])
            isplitr
            · ipureintro; rfl
            iintro %zsl2 ⟨Hz2, -⟩
            wp_auto
            wp_apply wp_slice_append $$ [$Hcsl1 $Hccap1 $Hz2] as %acsl' ⟨Hcsl1, Hccap1, -⟩
            wp_join_done
            iexists Aps ++ [bp], Bps', acsl', bcsl'
            simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
              List.nil_append]
            iframe
            iapply (ownNodes_app o c f less _ Aps [bp] Acs [y] Hapsl).2
            iframe
            rw [ownNodes_cons, ownNodes_nil]
            iframe
          · -- leaves
            have h0 : Bps = [] := by
              apply List.eq_nil_of_length_eq_zero; rw [Hbcl.1]; word
            subst h0
            have h0 : Bcs = [] := by simpa using Hbps.symm
            subst h0
            iexists Aps, [], acsl, bcsl
            simp only [List.take_nil, List.drop_nil, List.append_nil]
            iframe
          wp_join_done
          have hsr := steal_right (d := d) (h := h) Ais Bis' Acs Bcs w x Hd2 hsa hsb Hcil hdcr
          have hset : ((P ++ x :: Q).map Prod.fst).set (sint.Z i).toNat w.1 =
              (P ++ w :: Q).map Prod.fst := by
            rw [show (sint.Z i).toNat = P.length by word,
              show w.1 = Prod.fst w from rfl, ← List.map_set, set_mid]
          iexists (Tree.node (P ++ w :: Q) (Pc ++ Tree.node (Ais ++ [x]) (Acs ++ Bcs.take 1) ::
            Tree.node Bis' (Bcs.drop 1) :: Qc))
          iframe n typ minItems item
          isplitl
          · iapply ownedNode_close o c f less _ n _ _ (Pp ++ c1 :: c2 :: Qp) isl' csl'
            unfold ownedRes
            rw [hset]
            iframe
            isplitr
            · ipureintro; exact Hnn
            iapply (ownNodes_split2 o c f less _ Pp Qp Pc Qc c1 c2 _ _ (by omega)).2
            iframe
            isplitl [Hi1 Hc1 Hw1 Hisl1 Hicap1 Hcsl1 Hccap1 Hch1]
            · iapply ownNode_of_owned
              iapply ownedNode_close o c f less _ c1 _ _ Aps2 aisl' acsl2
              unfold ownedRes
              rw [show Ais.map Prod.fst ++ [x.1] = (Ais ++ [x]).map Prod.fst by simp]
              iframe
              ipureintro; exact Hnn1
            · iapply ownNode_of_owned
              iapply ownedNode_close o c f less _ c2 _ _ Bps2 bisl' bcsl2
              unfold ownedRes
              rw [show (List.map Prod.fst (w :: Bis')).take 0 ++
                  (List.map Prod.fst (w :: Bis')).drop (0 + 1) = Bis'.map Prod.fst by simp]
              iframe
              ipureintro; exact Hnn2
          · ipureintro
            exact grow_window tgt P Q Pc Qc x w _ _ _ _ (by omega) Hshape Hlen hsr.1 hsr.2.1 hsr.2.2
        | false =>
          have hnR : ¬ (sint.nat i < is.length ∧
              ∃ cr, cs[sint.nat i + 1]? = some cr ∧ d ≤ cr.items.length) :=
            fun hh => by simpa using Hb.2 hh
          clear Hb
          wp_auto
          -- merge child `j` with its right sibling, `j = i` or `i - 1`
          wp_join iprop(∃ j : w64, i_ptr ↦ j ∗ ⌜0 ≤ sint.Z j ∧ sint.nat j < is.length ∧
              (sint.nat j = sint.nat i ∨ (sint.nat j + 1 = sint.nat i ∧ sint.nat i = is.length))⌝)
            with [i] as ⟨%j, i, %Hj⟩
          · iexists (i - W64 1)
            iframe
            ipureintro
            simp at Hil
            exact ⟨by word, by word, .inr ⟨by word, by word⟩⟩
          · iexists i
            iframe
            ipureintro
            simp at Hil
            exact ⟨Hi0, by word, .inl rfl⟩
          obtain ⟨Hj0, Hjl, Hjc⟩ := Hj
          obtain ⟨Pc, a, b, Qc, hcs, hPc⟩ := rm_split2 cs (sint.nat j) (by omega)
          obtain ⟨Pp, pa, pb, Qp, hps, hPp⟩ := rm_split2 ps (sint.nat j) (by omega)
          obtain ⟨P, x, Q, his, hP⟩ := rm_split1 is (sint.nat j) Hjl
          subst hcs hps his
          have hsa := shape_child (c := a) Hshape (j := Pc.length) (by simp)
          have hsb := shape_child (c := b) Hshape (j := Pc.length + 1) (by simp)
          have hal : a.items.length ≤ d - 1 := by
            rcases Hjc with hj | ⟨hj, hi⟩
            · have : a = ci := by
                rw [← hj, ← hPc] at Hci; simp at Hci; exact Hci
              rw [this]; exact Hcil
            · rcases Nat.lt_or_ge a.items.length d with hlt | hge
              · omega
              · exact absurd ⟨by word, a,
                  by rw [show sint.nat i - 1 = Pc.length by omega]; simp, hge⟩ hnL
          have hbl : b.items.length ≤ d - 1 := by
            rcases Hjc with hj | ⟨hj, hi⟩
            · rcases Nat.lt_or_ge b.items.length d with hlt | hge
              · omega
              · exact absurd ⟨by simp; omega, b,
                  by rw [show sint.nat i + 1 = Pc.length + 1 by omega]; simp, hge⟩ hnR
            · have : b = ci := by
                rw [show sint.nat i = Pc.length + 1 by omega] at Hci; simp at Hci; exact Hci
              rw [this]; exact Hcil
          have hidx : remIdx o.lt tgt (P ++ Q) = P.length := by
            apply merge_remIdx o.order tgt P Q x hsi
            rcases Hjc with hj | ⟨hj, hi⟩
            · left; omega
            · right
              refine ⟨by omega, ?_⟩
              apply List.eq_nil_of_length_eq_zero
              simp at hi; omega
          icases (ownNodes_split2 o c f less _ Pp Qp Pc Qc pa pb a b (by omega)).1 $$ Hch
            with ⟨HP, Ha, Hb, HQ⟩
          ihave Hsh : nodeShallow (V := V) c (DFrac.own 1) n (P ++ x :: Q) (Pp ++ pa :: pb :: Qp)
            $$ [Hi Hc Hw Hisl Hicap Hcsl Hccap]
          · unfold nodeShallow nodeFields; iexists isl, csl; iframe; ipureintro; exact Hnn
          have hpa : (Pp ++ pa :: pb :: Qp)[sint.nat j]? = some pa := by
            rw [show sint.nat j = Pp.length by omega]; simp
          wp_apply wp_mutableChild o c f less n _ _ j pa a Hj0 hpa $$ [Hsh Ha] as %c1 ⟨Hsh, Hc1⟩
          · iframe # ∗
          rw [show sint.nat j = Pp.length by omega, set_mid0]
          unfold nodeShallow nodeFields
          icases Hsh with ⟨%isl', %csl', ⟨%_, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩
          cases a with
          | node Ais Acs =>
          cases b with
          | node Bis Bcs =>
          simp only [Tree.items_node] at hal hbl hsa hsb
          icases ownedNode_open o c f less _ c1 _ _ $$ Hc1 with ⟨%Aps, %aisl, %acsl, Hr1⟩
          unfold ownedRes
          icases Hr1 with ⟨%Hnn1, Hi1, Hc1, Hw1, Hisl1, Hicap1, Hcsl1, Hccap1, Hch1⟩
          icases ownNode_merge_acc o c f less pb Bis Bcs $$ Hb
            with ⟨%bisl, %bcsl, %dqb, %bps, Hbi, Hbc, Hbisl, Hbcsl, Hbch, Hbfree⟩
          ihave %Hapsl := ownNodes_length o c f less _ _ _ $$ Hch1
          have hx : ((P ++ x :: Q).map Prod.fst)[sint.nat j]? = some x.1 := by
            rw [show sint.nat j = P.length by omega]; simp
          wp_apply wp_removeAt (structFieldRef (node V) go!"items" n) isl'
            ((P ++ x :: Q).map Prod.fst) j x.1 Hj0 hx $$ [Hi Hisl Hicap] as %isl'' ⟨Hi, Hisl, Hicap⟩
          · iframe
          have hpb : (Pp ++ c1 :: pb :: Qp)[sint.nat (j + W64 1)]? = some pb := by
            rw [show sint.nat (j + W64 1) = Pp.length + 1 by word]; simp
          wp_apply wp_removeAt (structFieldRef (node V) go!"children" n) csl'
            (Pp ++ c1 :: pb :: Qp) (j + W64 1) pb (by word) hpb
            $$ [Hc Hcsl Hccap] as %csl'' ⟨Hc, Hcsl, Hccap⟩
          · iframe
          wp_apply wp_slice_literal (l := [x.1])
          isplitr
          · ipureintro; rfl
          iintro %zsl ⟨Hz, -⟩
          wp_auto
          wp_apply wp_slice_append $$ [$Hisl1 $Hicap1 $Hz] as %aisl' ⟨Hisl1, Hicap1, -⟩
          wp_apply wp_slice_append $$ [$Hisl1 $Hicap1 $Hbisl] as %aisl'' ⟨Hisl1, Hicap1, Hbisl⟩
          wp_apply wp_slice_append $$ [$Hcsl1 $Hccap1 $Hbcsl] as %acsl' ⟨Hcsl1, Hccap1, Hbcsl⟩
          ihave Hfree := Hbfree $$ [Hbi Hbc Hbisl Hbcsl]
          · iframe
          unfold freePre
          wp_apply wp_freeNode o c f less pb $$ [Hfree] as %r -
          · iframe # ∗
          have hmt := merge_trees (d := d) (h := h) Ais Bis Acs Bcs x Hd2 hsa hsb hal hbl
          have hisl : ((P ++ x :: Q).map Prod.fst).take (sint.nat j) ++
              ((P ++ x :: Q).map Prod.fst).drop (sint.nat j + 1) = (P ++ Q).map Prod.fst := by
            rw [show sint.nat j = (P.map Prod.fst).length by simp; omega, List.map_append,
              List.map_cons, take_drop_mid, List.map_append]
          have hcsl : (Pp ++ c1 :: pb :: Qp).take (sint.nat (j + W64 1)) ++
              (Pp ++ c1 :: pb :: Qp).drop (sint.nat (j + W64 1) + 1) = Pp ++ c1 :: Qp := by
            rw [show sint.nat (j + W64 1) = Pp.length + 1 by word, take_drop_mid1]
          rw [hisl, hcsl]
          wp_join_done
          iexists (Tree.node (P ++ Q) (Pc ++ Tree.node (Ais ++ x :: Bis) (Acs ++ Bcs) :: Qc))
          iframe n typ minItems item
          isplitl
          · iapply ownedNode_close o c f less _ n _ _ (Pp ++ c1 :: Qp) isl'' csl''
            unfold ownedRes
            iframe
            isplitr
            · ipureintro; exact Hnn
            iapply (ownNodes_split1 o c f less _ Pp Qp Pc Qc c1 _ (by omega)).2
            iframe
            iapply ownNode_of_owned
            iapply ownedNode_close o c f less _ c1 _ _ (Aps ++ bps) aisl'' acsl'
            unfold ownedRes
            rw [show Ais.map Prod.fst ++ [x.1] ++ Bis.map Prod.fst =
              (Ais ++ x :: Bis).map Prod.fst by simp]
            iframe
            isplitr
            · ipureintro; exact Hnn1
            iapply (ownNodes_app o c f less _ Aps bps Acs Bcs Hapsl).2
            iframe
          · ipureintro
            exact grow_merge tgt P Q Pc Qc x _ _ _ (by omega) Hshape Hlen hmt.1 hmt.2 hidx
    · obtain ⟨hs, he, hl, hint, -⟩ := id Hmid
      wp_apply IHr $$ %n %t'' %item %tgt %minItems %typ %d %(h + 1) [] [Hn]
        as %out %fnd ⟨%t', Hn', %Hpost⟩
      · ipureintro
        exact ⟨hs, he ▸ Hsorted, hl, Hmin, Hd2, Hd62, Htyp, fun h0 => absurd h0 (by omega),
          fun _ => hint⟩
      · rw [he]
        iframe # ∗
      iapply HΦ
      iexists t'
      iframe
      ipureintro
      exact grow_final (by omega) Hmid Hpost

end loeb

theorem node.remove.wp_proof (wp_find : items.find.spec (GF := GF) (hG := hG))
    (wp_removeAt : items.removeAt.spec (GF := GF) (hG := hG))
    (wp_pop : items.pop.spec (GF := GF) (hG := hG))
    (wp_insertAt : items.insertAt.spec (GF := GF) (hG := hG))
    (wp_mutableChild : node.mutableChild.spec (GF := GF) (hG := hG))
    (wp_freeNode : copyOnWriteContext.freeNode.spec (GF := GF) (hG := hG)) :
    node.remove.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n t item tgt minItems typ d h Hshape Hsorted Hlen Hmin Hd2 Hd62
    Htyp Hleaf Hint
  have H := (remove_grow (T := T) o c f less wp_find wp_removeAt wp_pop wp_insertAt
    wp_mutableChild wp_freeNode).trans and_elim_l
  unfold removeI RemPost at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %trivial %n %t %item %tgt %minItems %typ %d %h [] [HP] HΦ
  · ipureintro; exact ⟨Hshape, Hsorted, Hlen, Hmin, Hd2, Hd62, Htyp, Hleaf, Hint⟩
  · iexact HP

theorem node.growChildAndRemove.wp_proof (wp_find : items.find.spec (GF := GF) (hG := hG))
    (wp_removeAt : items.removeAt.spec (GF := GF) (hG := hG))
    (wp_pop : items.pop.spec (GF := GF) (hG := hG))
    (wp_insertAt : items.insertAt.spec (GF := GF) (hG := hG))
    (wp_mutableChild : node.mutableChild.spec (GF := GF) (hG := hG))
    (wp_freeNode : copyOnWriteContext.freeNode.spec (GF := GF) (hG := hG)) :
    node.growChildAndRemove.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less n t item tgt i minItems typ d h ci Hshape Hh Hsorted Hlen H1 Hmin
    Hd2 Hd62 Htyp Hi0 Hir Hci Hcil
  have H := (remove_grow (T := T) o c f less wp_find wp_removeAt wp_pop wp_insertAt
    wp_mutableChild wp_freeNode).trans and_elim_r
  unfold growI at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %trivial %n %t %item %tgt %i %minItems %typ %d %h %ci [] [HP] HΦ
  · ipureintro; exact ⟨Hshape, Hh, Hsorted, Hlen, H1, Hmin, Hd2, Hd62, Htyp, Hi0, Hir, Hci, Hcil⟩
  · iexact HP

end proof

end Btree
end EtcdGrove
end Perennial
