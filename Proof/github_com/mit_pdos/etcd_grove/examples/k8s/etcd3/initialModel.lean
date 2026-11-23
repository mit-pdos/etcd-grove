module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialModel
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewEmptyModel
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore item)

section pure
variable [GooseExts]

theorem ofList_snoc_fresh {V : Type} (l : List (GoString × V)) (k : GoString) (v : V)
    (h : k ∉ l.map Prod.fst) : GMap.ofList (l ++ [(k, v)]) = <[k := v]> (GMap.ofList l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show <[a.1 := a.2]> (GMap.ofList (l ++ [(k, v)])) = <[k := v]> (<[a.1 := a.2]> (GMap.ofList l))
    rw [ih h.2]
    exact GMap.insert_commute _ _ _ (fun e => h.1 e.symm)

/-- The items of a prefix of the store, at their store keys. -/
abbrev itemsOf (l : List item) : GMap GoString github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj :=
  GMap.ofList (l.map fun it => (storeKeyL it.key', it.obj'))

/-- The rewrite flags of a prefix of the store. -/
abbrev rewritesOf (l : List item) : GMap GoString Bool :=
  GMap.ofList ((l.filter fun it => !it.canon').map fun it => (storeKeyL it.key', true))

theorem itemsOf_snoc (l : List item) (it : item) (h : storeKeyL it.key' ∉ l.map fun it => storeKeyL it.key') :
    itemsOf (l ++ [it]) = <[storeKeyL it.key' := it.obj']> (itemsOf l) := by
  unfold itemsOf
  rw [List.map_append]
  apply ofList_snoc_fresh
  simpa [List.map_map] using h

theorem rewritesOf_snoc (l : List item) (it : item)
    (h : storeKeyL it.key' ∉ l.map fun it => storeKeyL it.key') :
    rewritesOf (l ++ [it]) =
      if it.canon' then rewritesOf l else <[storeKeyL it.key' := true]> (rewritesOf l) := by
  unfold rewritesOf
  rw [List.filter_append]
  cases hc : it.canon'
  · simp only [List.filter_cons, List.filter_nil, hc, Bool.not_false, ↓reduceIte, List.map_append,
      List.map_cons, List.map_nil, Bool.false_eq_true]
    apply ofList_snoc_fresh
    intro hm
    apply h
    simp only [List.map_map, List.mem_map, List.mem_filter] at hm ⊢
    obtain ⟨a, ⟨ha, -⟩, he⟩ := hm
    exact ⟨a, ha, he⟩
  · simp [hc]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem initialModel.wp_proof
    (wp_NewEmptyModel : k8s_correctness.NewEmptyModel.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG)) :
    initialModel.spec (GF := GF) (hG := hG) := by
  intro s0 st hnd hlen
  wp_start as #Hs
  iunfold storeOwn at Hs
  icases Hs with ⟨#Hits, %Hrv⟩
  ihave %Hl := ownSlice_len $$ Hits
  wp_auto
  wp_apply wp_NewEmptyModel as %mp %il ⟨Hmp, Hil⟩
  wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %rl Hrl
  (try wp_auto)
  ihave HI : (∃ (j : w64) (itv : item) (M : GMap GoString GoInterface),
      "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ itv ∗
      "Hmp" ∷ mp ↦ modelVal il rl (absR st) ∗
      "Hil" ∷ il ↦$ M ∗ "Hrl" ∷ rl ↦$ rewritesOf (st.items.take (sint.nat j)) ∗
      "#HD" ∷ itemsRO M (itemsOf (st.items.take (sint.nat j))) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s0.items'.len⌝ : IProp GF)
    $$ [i it Hmp Hil Hrl]
  · iexists W64 0, _, ∅
    ihave #HD := itemsRO_empty (GF := GF)
    iframe
    isplitl [Hmp]
    · iExactEq Hmp
      unfold modelVal absR
      rw [← Hrv]
    isplitr
    · simp only [named]
      iExactEq HD
      simp [show sint.nat (0#64 : w64) = 0 from rfl, itemsOf, GMap.ofList]; rfl
    ipureintro; word
  wp_for HI
  by_cases Hif : sint.Z j < sint.Z s0.items'.len
  · (try simp only [decide_eq_true Hif, ↓reduceIte])
    (try simp only [eq_self_iff_true, decide_true, ↓reduceIte])
    wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s0.items'.len := ⟨Hj.1, Hif⟩
    list_elem st.items (sint.nat j) as it
    (try simp only [Hb', _root_.and_self, ↓reduceIte])
    (try simp only [decide_True_any, ↓reduceIte])
    wp_apply wp_load_slice_index s0.items' (sint.Z j) st.items _ it Hj.1 $$ [Hits] as -
    · iframe #; ipureintro; exact Hit_lookup
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := Hb'.1; have := Hb'.2; have := Hl.2; word
    have htake : st.items.take (sint.nat (j + W64 1)) = st.items.take (sint.nat j) ++ [it] := by
      rw [hj1, List.take_add_one, Hit_lookup]; rfl
    have hfresh : storeKeyL it.key' ∉ (st.items.take (sint.nat j)).map fun it => storeKeyL it.key' := by
      intro hm
      have hnd' := hnd
      rw [← List.take_append_drop (sint.nat j + 1) st.items, ← hj1, htake, List.map_append,
        List.map_append] at hnd'
      have := (List.nodup_append.1 (List.nodup_append.1 hnd').1).2.2
      exact this _ hm _ (by simp) rfl
    (try wp_auto)
    ipersist o
    wp_apply wp_storeKey
    unfold modelVal
    (try wp_auto)
    wp_apply (wp_mapInsert go.string il M (storeKeyL it.key')
      (interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty.PointerType #o_ptr)) $$ Hil as Hil
    (try wp_auto)
    have hsz' : GMap.size (<[storeKeyL it.key' := it.obj']> (itemsOf (st.items.take (sint.nat j)))) ≤
        2 ^ 62 := by
      rw [← itemsOf_snoc _ it hfresh, ← htake]
      have h1 := size_ofList_le ((st.items.take (sint.nat (j + W64 1))).map
        fun it => (storeKeyL it.key', it.obj'))
      have h2 : ((st.items.take (sint.nat (j + W64 1))).map
          fun it => (storeKeyL it.key', it.obj')).length ≤ st.items.length := by
        rw [List.length_map, List.length_take]; exact Nat.min_le_right _ _
      unfold itemsOf; omega
    ihave #HD' := itemsRO_insert M _ (storeKeyL it.key') o_ptr it.obj' hsz' $$ [HD o]
    · iframe #
    have hitems := itemsOf_snoc _ it hfresh
    have hrw := rewritesOf_snoc _ it hfresh
    rw [← htake] at hitems hrw
    cases hc : it.canon'
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hrw
      simp only [Bool.not_false]
      wp_auto
      wp_apply wp_storeKey
      (try wp_auto)
      wp_apply (wp_mapInsert go.string rl _ (storeKeyL it.key') true) $$ Hrl as Hrl
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, _
      rw [hrw, hitems]
      iframe
      isplitr
      · iexact HD'
      ipureintro; have := Hb'.1; have := Hb'.2; word
    · simp only [hc, ↓reduceIte] at hrw
      simp only [Bool.not_true]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, _
      rw [hrw, hitems]
      iframe
      isplitr
      · iexact HD'
      ipureintro; have := Hb'.1; have := Hb'.2; word
  · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte])
    (try simp only [decide_eq_false false_neq_true, Bool.false_eq_true, ↓reduceIte]); wp_pures
    cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
    (try simp only [decide_True_any, ↓reduceIte])
    (try wp_auto)
    have hfull : st.items.take (sint.nat j) = st.items := List.take_of_length_le (by word)
    rw [hfull]
    iapply HΦ
    unfold modelOwn modelRep
    iframe Hpkg
    iexists il, rl, M
    iframe
    iExactEq HD
    rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
