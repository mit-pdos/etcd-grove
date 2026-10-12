module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.node__get
public import Spec.k8s_io.utils.third_party.forked.golang.btree.items__find
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

theorem node.get.wp_proof (wp_find : items.find.spec (GF := GF) (hG := hG)) :
    node.get.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o c f less dq n t key k d h
  induction h using Nat.strongRecOn generalizing n t with
  | _ h IH =>
  intro hshape hsorted
  obtain ⟨is, cs⟩ := t
  have hok := shapeOk_of_shape hshape
  wp_start as ⟨#Hcow, Hn, #Hkey, #Hitems⟩
  icases ownNode_read o c f less dq n is cs $$ [Hn] with
    ⟨%dq', %isl, %csl, %cow, %ps, Hnf, #Hcow', Hisl, Hcsl, Hch, Hclose⟩
  · iframe Hn Hcow
  unfold nodeFields
  icases Hnf with ⟨Hnn, Hfi, Hfc, Hfw⟩
  ihave #Hless := isCow_less o f less cow $$ Hcow'
  wp_alloc_anon
  wp_pures
  wp_alloc_anon
  wp_auto
  have hsi : Sorted o.lt is := Sorted.sublist (items_sublist_elemsAux is cs) (by simpa using hsorted)
  ihave #HisLess := isCow_isLess o f less cow $$ Hcow'
  ihave #HitemsIs := allItems_mono o (l1 := is) (l2 := (Tree.node is cs).elems)
    (fun e he => by simpa using (items_sublist_elemsAux is cs).subset he) $$ Hitems
  wp_apply wp_find o isl is dq' key k less hsi $$ [Hisl] as %idx %found ⟨Hisl, %Hres⟩
  · iframe # ∗
  obtain ⟨Hidx, Hidx0, Hfound⟩ := Hres
  ihave %Hlen := ownSlice_len _ _ _ $$ Hisl
  simp only [List.length_map] at Hlen
  ihave %Hlenc := ownSlice_len _ _ _ $$ Hcsl
  ihave %Hlenps := ownNodes_length o c f less dq ps cs $$ Hch
  have hsorted' : Sorted o.lt (Tree.elemsAux is cs) := by simpa using hsorted
  wp_if_destruct
  · -- not found
    have hnf : ¬ ∃ e, is[countLt o.lt is k]? = some e ∧ e.2 = k := by
      rw [← Hidx]; intro hh; exact absurd (Hfound.2 hh) (by simp)
    have hlk := lookup_node_not_found o.order is cs k hok hsorted' hnf
    wp_if_destruct
    · -- an internal node: descend into child `idx`
      have hcs : cs ≠ [] := by
        intro hc; rw [hc] at Hlenps
        have h0 : ps.length = 0 := by simpa using Hlenps
        word
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
        cases h with
        | zero => exact absurd (by simpa [Tree.Shape] using hshape) hcs
        | succ h' => exact ⟨h', rfl⟩
      have hcl : cs.length = is.length + 1 := hshape.1
      have hjc : sint.nat idx < cs.length := by
        have := countLt_le (lt := o.lt) is k; omega
      list_elem ps (sint.nat idx) as p
      list_elem cs (sint.nat idx) as ch
      have hb : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z csl.len := by word
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index csl (sint.Z idx) ps dq' p Hidx0 $$ [Hcsl] as Hcsl
      · iframe; ipureintro; exact Hp_lookup
      icases (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).1 $$ Hch
        with ⟨Hc, Hch⟩
      have hchs : ch.Shape d h' := (hshape.2 ch (List.mem_of_getElem? Hch_lookup)).2
      have hdec := elems_decomp (countLt o.lt is k) is cs hok (countLt_le is k)
      have hsub : ch.elems.Sublist (Tree.elemsAux is cs) := by
        rw [hdec, ← Hidx, chElems_eq Hch_lookup]
        exact ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
      ihave #HitemsC := allItems_mono o (l1 := ch.elems) (l2 := (Tree.node is cs).elems)
        (fun e he => by simpa using hsub.subset he) $$ Hitems
      wp_apply (IH h' (by omega) p ch hchs (Sorted.sublist hsub hsorted')) $$ [Hc] as Hc
      · iframe # ∗
      rw [Tree.elems_node, hlk, ← Hidx, chElems_eq Hch_lookup]
      iapply HΦ
      iapply Hclose
      iframe
      iapply (ownNodes_extract o c f less dq ps cs _ p ch Hp_lookup Hch_lookup).2
      iframe
    · -- a leaf
      have hcs : cs = [] := by
        cases cs with
        | nil => rfl
        | cons _ _ =>
          have h0 : 0 < ps.length := by simp [Hlenps]
          word
      subst hcs
      rw [Tree.elems_node, hlk, chElems_of_nil]
      simp only [lookup, List.find?_nil, Option.map_none, Option.getD_none, Option.isSome_none]
      iapply HΦ
      iapply Hclose
      iframe
  · -- found
    obtain ⟨e, he, hek⟩ := Hfound.1 rfl
    have hlt : sint.nat idx < is.length := (List.getElem?_eq_some_iff.1 he).1
    have hb : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z isl.len := by word
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index isl (sint.Z idx) (is.map Prod.fst) dq' e.1 Hidx0 $$ [Hisl] as Hisl
    · iframe; ipureintro
      rw [show (sint.Z idx).toNat = sint.nat idx from rfl, List.getElem?_map, he]; rfl
    have hmem : e ∈ Tree.elemsAux is cs :=
      (items_sublist_elemsAux is cs).subset (List.mem_of_getElem? he)
    rw [Tree.elems_node, ← hek, lookup_of_mem o.order hsorted' hmem]
    simp only [Option.getD_some, Option.isSome_some]
    iapply HΦ
    iapply Hclose
    iframe

end proof

end btree
end EtcdGrove
end Perennial
