/-
A bucket's tokens before its nodes are spilled (`Bucket.spill`, after its opened buckets were):
from the write path's form (`bktToks`: each position's tokens, the opened buckets' trees held
apart) and the opened buckets' results (`kidRes`: a changed one's new value, put into the leaf
holding its entry; an unchanged one's old tree), the form `node.spill` takes (`rtoks`: each
node's page token and its entries' written trees and values), and the nodes' facts (`nodeU`,
`subU`: `ready_of_shape`). A bucket with no materialized root gets its old tree's tokens back
(`old_of_shape`). Each opened bucket's entry is at one leaf (`SpillKeys.lean`), so its result
goes to the position holding it.
-/
module

public import Proof.go_etcd_io.bbolt.SpillNode
public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Proof.go_etcd_io.bbolt.ShapeOpen
public import Proof.go_etcd_io.bbolt.RebalanceFree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common
open ShapeOpen

/-! ### Big separating conjunctions: splitting a map, a map as a list of keys -/

section gen
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

theorem gmap_filter_eq' {K V : Type} [DecidableEq K] (p : K → V → Bool) (m : GMap K V) :
    GMap.filter p m = Iris.Std.PartialMap.filter p m := by
  refine GMap.ext (fun k => ?_)
  rw [GMap.lookup_filter]
  show _ = Iris.Std.PartialMap.get? (Iris.Std.PartialMap.filter p m) k
  rw [Iris.Std.LawfulPartialMap.get?_filter]
  change _ = (m !! k).bind _
  cases m !! k <;> rfl

theorem bigSepM_filter_split {K V : Type} [DecidableEq K] (Φ : K → V → IProp GF) (p : K → Bool)
    (m : GMap K V) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢
      ([∗map] k ↦ x ∈ GMap.filter (fun k _ => p k) m, Φ k x) ∗
      [∗map] k ↦ x ∈ GMap.filter (fun k _ => !p k) m, Φ k x := by
  rw [gmap_filter_eq', gmap_filter_eq']
  refine BiEntails.trans ?_ (sep_congr
    (BiEntails.of_eq (BigSepM.bigSepM_filter_cond (Φ := Φ) (fun k _ => p k))).symm
    (BiEntails.of_eq (BigSepM.bigSepM_filter_cond (Φ := Φ) (fun k _ => !p k))).symm)
  rw [← BigSepM.bigSepM_sep_eq]
  constructor
  · refine BigSepM.bigSepM_mono_of_forall (fun {k x} => ?_)
    cases h : p k
    · simp only [h, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; exact emp_sep.2
    · simp only [h, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]; exact sep_emp.2
  · refine BigSepM.bigSepM_mono_of_forall (fun {k x} => ?_)
    cases h : p k
    · simp only [h, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; exact emp_sep.1
    · simp only [h, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]; exact sep_emp.1

theorem gmap_empty_of {K V : Type} [DecidableEq K] (m : GMap K V) (h : ∀ k, m !! k = none) :
    m = ∅ := GMap.ext (fun k => by rw [show GMap.lookup m k = m !! k from rfl, h k]; rfl)

theorem bigSepM_none {K V : Type} [DecidableEq K] (Φ : K → V → IProp GF) (m : GMap K V)
    (h : ∀ k, m !! k = none) : ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ emp := by
  rw [gmap_empty_of m h]
  exact BigSepM.bigSepM_empty

/-- A map split by an owner `f` of its keys (in the list `S`). -/
theorem bigSepM_partition {K V J : Type} [DecidableEq K] [DecidableEq J] (Φ : K → V → IProp GF)
    (f : K → J) :
    ∀ (S : List J) (m : GMap K V), S.Nodup → (∀ k x, m !! k = some x → f k ∈ S) →
      ([∗map] k ↦ x ∈ m, Φ k x) ⊢
        [∗list] l ∈ S, [∗map] k ↦ x ∈ GMap.filter (fun k _ => decide (f k = l)) m, Φ k x := by
  intro S
  induction S with
  | nil =>
    intro m _ h
    refine (bigSepM_none Φ m (fun k => ?_)).1.trans ?_
    · cases hk : m !! k with
      | none => rfl
      | some x => exact absurd (h k x hk) (by simp)
    · exact (BigSepL.bigSepL_nil (PROP := IProp GF)).2
  | cons l S ih =>
    intro m hnd h
    refine (bigSepM_filter_split Φ (fun k => decide (f k = l)) m).1.trans ?_
    refine BIBase.Entails.trans ?_ (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    refine sep_mono .rfl ?_
    have hnd' := (List.nodup_cons.1 hnd)
    refine (ih _ hnd'.2 (fun k x hk => ?_)).trans (BigSepL.bigSepL_mono (fun {j l'} hl' => ?_))
    · rw [GMap.lookup_filter] at hk
      cases hm : m !! k with
      | none => rw [hm] at hk; cases hk
      | some y =>
        rw [hm] at hk
        simp only [Option.filter] at hk
        have hne : f k ≠ l := by
          intro e; simp [e] at hk
        rcases List.mem_cons.1 (h k y hm) with e | e
        · exact absurd e hne
        · exact e
    · have hl'S : l' ∈ S := List.mem_of_getElem? hl'
      have hne : l' ≠ l := fun e => hnd'.1 (e ▸ hl'S)
      have e : GMap.filter (fun k _ => decide (f k = l'))
          (GMap.filter (fun k _ => !decide (f k = l)) m) =
          GMap.filter (fun k _ => decide (f k = l')) m := by
        refine GMap.ext (fun k => ?_)
        show (GMap.filter _ _) !! k = (GMap.filter _ _) !! k
        rw [GMap.lookup_filter, GMap.lookup_filter, GMap.lookup_filter]
        cases m !! k with
        | none => rfl
        | some y =>
          by_cases h1 : f k = l'
          · have h2 : f k ≠ l := fun e => hne (h1.symm.trans e)
            simp [Option.filter, h1, hne, Ne.symm hne]
          · by_cases h2 : f k = l <;> simp [Option.filter, h1, h2, Ne.symm hne]
      rw [e]

/-- A map whose keys are the list `L` (without duplicates), its values ignored. -/
theorem bigSepM_keys {K V : Type} [DecidableEq K] (Φ : K → IProp GF) :
    ∀ (L : List K) (m : GMap K V), L.Nodup → (∀ k, (m !! k).isSome ↔ k ∈ L) →
      ([∗map] k ↦ _x ∈ m, Φ k) ⊣⊢ [∗list] k ∈ L, Φ k := by
  intro L
  induction L with
  | nil =>
    intro m _ h
    refine (bigSepM_none (fun k _ => Φ k) m (fun k => ?_)).trans
      (BigSepL.bigSepL_nil (PROP := IProp GF)).symm
    cases hk : m !! k with
    | none => rfl
    | some x => exact absurd ((h k).1 (by rw [hk]; rfl)) (by simp)
  | cons k L ih =>
    intro m hnd h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((h k).2 (List.mem_cons_self))
    refine (BigSepM.bigSepM_delete (M := GMap K) (Φ := fun k _ => Φ k)
      (show Std.get? m k = some x from hx)).trans ?_
    refine BiEntails.trans ?_ (BigSepL.bigSepL_cons (PROP := IProp GF)).symm
    refine sep_congr .rfl (ih _ (List.nodup_cons.1 hnd).2 (fun k' => ?_))
    show (GMap.delete k m !! k').isSome ↔ k' ∈ L
    by_cases e : k' = k
    · subst e
      rw [GMap.lookup_delete]
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      exact (List.nodup_cons.1 hnd).1
    · rw [GMap.lookup_delete_ne _ (Ne.symm e), h k']
      simp [e]

/-- The keys of the entries of `ws` with `P`, as a list over `ws`. -/
theorem bigSepL_filter_keys {A K : Type} (Φ : K → IProp GF) (key : A → K) (P : A → Bool) :
    ∀ (ws : List A), ([∗list] k ∈ (ws.filter P).map key, Φ k) ⊣⊢
      [∗list] w ∈ ws, if P w then Φ (key w) else emp := by
  intro ws
  induction ws with
  | nil => simp
  | cons w ws ih =>
    by_cases hp : P w = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons]
      refine (BigSepL.bigSepL_cons (PROP := IProp GF)).trans ?_
      refine BiEntails.trans ?_ (BigSepL.bigSepL_cons (PROP := IProp GF)
        (Φ := fun _ w => if P w then Φ (key w) else emp)).symm
      simp only [hp, ite_true]
      exact sep_congr .rfl ih
    · simp only [List.filter_cons, hp, Bool.false_eq_true, if_false]
      refine ih.trans ?_
      refine BiEntails.trans ?_ (BigSepL.bigSepL_cons (PROP := IProp GF)
        (Φ := fun _ w => if P w then Φ (key w) else emp)).symm
      simp only [hp, Bool.false_eq_true, ite_false]
      exact emp_sep.symm

/-- Tokens of two sets of pages of `pages` (by predicates): the tokens of the pages of either. -/
theorem pgToks_or (γ : GName) (pages : GMap Nat (List w8)) (P1 P2 : Nat → Prop) :
    pgToks (GF := GF) γ (pagesWith pages P1) ∗ pgToks γ (pagesWith pages P2) ⊢
      pgToks γ (pagesWith pages (fun d => P1 d ∨ P2 d)) := by
  refine (sep_mono (pgToks_with γ pages P1).1 (pgToks_with γ pages P2).1).trans ?_
  refine BIBase.Entails.trans ?_ (pgToks_with γ pages _).2
  refine (BiEntails.of_eq BigSepM.bigSepM_sep_eq.symm).1.trans ?_
  refine BigSepM.bigSepM_mono (fun {d _} _ => ?_)
  by_cases h1 : P1 d <;> by_cases h2 : P2 d <;> simp [h1, h2]
  · iintro ⟨Ha, Hb⟩
    ihave %Hne := ghostMapElem_ne (GF := GF) γ d d (DFrac.own 1) () () $$ Ha Hb
    exact absurd rfl Hne
  · exact sep_emp.1
  · exact emp_sep.1
  · exact sep_emp.1

theorem pgToks_none (γ : GName) (pages : GMap Nat (List w8)) :
    ⊢ pgToks (GF := GF) γ (pagesWith pages (fun _ => False)) := by
  refine BIBase.Entails.trans ?_ (pgToks_with γ pages _).2
  simp only [decide_false, Bool.false_eq_true, ite_false]
  exact (BigSepM.bigSepM_emp (M := GMap Nat) (m := pages)).2

/-- Tokens of a family of sets of pages over a list: the tokens of their union. -/
theorem pgToks_family {K : Type} (γ : GName) (pages : GMap Nat (List w8)) (P : K → Nat → Prop) :
    ∀ (L : List K), ([∗list] k ∈ L, pgToks (GF := GF) γ (pagesWith pages (P k))) ⊢
      pgToks γ (pagesWith pages (fun d => ∃ k ∈ L, P k d)) := by
  intro L
  induction L with
  | nil =>
    iintro _
    iapply pgToks_mono γ pages (fun _ => False) _ (fun d h => by simp at h)
    iapply pgToks_none
  | cons k L ih =>
    refine (BigSepL.bigSepL_cons (PROP := IProp GF)).1.trans ?_
    refine (sep_mono .rfl ih).trans ?_
    refine (pgToks_or γ pages _ _).trans ?_
    exact pgToks_mono γ pages _ _ (fun d h => by
      obtain ⟨k', hk', hp⟩ := h
      rcases List.mem_cons.1 hk' with e | e
      · subst e; exact Or.inl hp
      · exact Or.inr ⟨k', e, hp⟩)

end gen

/-! ### Where an opened bucket's entry is: one leaf of the bucket -/

section wherek
variable [ext : FfiSyntax]

theorem tkp_under (W : WView) (B : BRec) :
    ∀ pid e, underPos W B pid e → ∀ lo hi, tkp W B pid lo hi → ∃ lo' hi', tkp W B e lo' hi' := by
  intro pid e h
  induction h with
  | self pid => intro lo hi ht; exact ⟨lo, hi, ht⟩
  | child pid cs i c pid' hk hc _ ih =>
    intro lo hi ht
    cases ht with
    | leaf _ ks _ _ hk' _ _ _ => exact (kidsAt_leaf_branch W B pid [] cs hk' hk).elim
    | branch _ ks cs' _ _ hk' _ _ _ _ hch =>
      rw [hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hk'
      subst hk'
      exact ih _ _ (hch i c hc)

theorem tkp_sorted (W : WView) (B : BRec) (e : w64) (lo hi : Option (List w8))
    (h : tkp W B e lo hi) : ∃ ks, keysAt W B e = some ks ∧ keysSorted ks := by
  cases h with
  | leaf _ ks _ _ _ hk hs _ => exact ⟨ks, hk, hs⟩
  | branch _ ks _ _ _ _ hk hs _ _ _ => exact ⟨ks, hk, hs⟩

theorem sorted_idx (L : List (List w8)) (hs : keysSorted L) (i j : Nat) (a : List w8)
    (hi : L[i]? = some a) (hj : L[j]? = some a) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd (hs i j a a h hi hj) (goStringLt_irrefl_r a)
  · exact h
  · exact absurd (hs j i a a h hj hi) (goStringLt_irrefl_r a)

/-- Two entries with one key of a sorted list of entries are one. -/
theorem ws_key_unique (ws : List WEntry) (hs : keysSorted (ws.map WEntry.key)) (w1 w2 : WEntry)
    (h1 : w1 ∈ ws) (h2 : w2 ∈ ws) (hk : w1.key = w2.key) : w1 = w2 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h2
  have hi' : (ws.map WEntry.key)[i]? = some w1.key := by rw [List.getElem?_map, hi]; rfl
  have hj' : (ws.map WEntry.key)[j]? = some w1.key := by rw [List.getElem?_map, hj, hk]; rfl
  have := sorted_idx _ hs i j _ hi' hj'
  subst this; rw [hi] at hj; exact Option.some.inj hj

/-- A bucket's nested buckets' entries with one key have one value. -/
theorem entryIn_unique (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (k v1 v2 : List w8) (h1 : entryIn W B k v1)
    (h2 : entryIn W B k v2) : v1 = v2 := by
  have ht := tkp_root W hwm bl B bnd hv hc hk hr
  obtain ⟨e1, hu1, hl1, hp1⟩ := entryIn_posK W hwm bl B hv hc hr k v1 h1
  obtain ⟨e2, hu2, hl2, hp2⟩ := entryIn_posK W hwm bl B hv hc hr k v2 h2
  have he := leafHas_unique W B k _ _ _ ht e1 e2 hu1 hu2 hl1 hl2
  subst he
  obtain ⟨lo, hi, hte⟩ := tkp_under W B _ _ hu1 _ _ ht
  obtain ⟨ks, hks, hsort⟩ := tkp_sorted W B _ _ _ hte
  cases hres : resolve B e1 with
  | some l =>
    have hks' := hks
    unfold keysAt at hks'
    rw [hres] at hks'
    cases hr' : B.ns !! l with
    | none => simp only [hr', Option.map_none] at hks'; cases hks'
    | some r =>
      obtain ⟨w1, hw1, hk1, hv1, -⟩ := hp1.1 l r hres hr'
      obtain ⟨w2, hw2, hk2, hv2, -⟩ := hp2.1 l r hres hr'
      rw [keysAt_node W B _ l r hres hr'] at hks
      cases hks
      rw [← hv1, ← hv2, ws_key_unique r.ws hsort w1 w2 hw1 hw2 (hk1.trans hk2.symm)]
  | none =>
    obtain ⟨lp, i, hwp, hi, hk1, hv1, -⟩ := hp1.2 hres
    obtain ⟨lp', i', hwp', hi', hk2, hv2, -⟩ := hp2.2 hres
    rw [hwp] at hwp'; cases hwp'
    obtain ⟨p, pg⟩ := lp
    rw [keysAt_page W B _ p pg hres hwp] at hks
    cases hks
    have hka := kidsAt_page W B _ p pg hres hwp
    rw [hl1.1] at hka
    simp only [Option.some.injEq, Prod.mk.injEq] at hka
    have hleaf : pageFlags pg = leafPageFlag := of_decide_eq_true hka.1.symm
    have hpk : ∀ j, pageKey pg j = leafKey pg j := fun j => by unfold pageKey; rw [if_pos hleaf]
    have e1 : ((List.range (pageCount pg)).map (pageKey pg))[i]? = some k := by
      rw [List.getElem?_map, List.getElem?_range hi]; simp [hpk, hk1]
    have e2 : ((List.range (pageCount pg)).map (pageKey pg))[i']? = some k := by
      rw [List.getElem?_map, List.getElem?_range hi']; simp [hpk, hk2]
    have := sorted_idx _ hsort i i' k e1 e2
    subst this
    rw [← hv1, ← hv2]

/-- A leaf node holding an entry: its position, under the root. -/
theorem pos_leaf (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hr : bktRanked B) (l : Loc) (r : NRec) (hrl : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (k : List w8) (hk : ∃ w ∈ r.ws, w.key = k) :
    resolve B r.nv.pgid' = some l ∧ underPos W B B.ib.root' r.nv.pgid' ∧
      leafHas W B r.nv.pgid' k := by
  obtain ⟨rk, N, hrk⟩ := hr
  have hcl := hc.2.2.2.2.2.2.2.1 l r hrl
  have hnml : B.nm !! r.nv.pgid' = some l := hcl.2.2.2.2.2.2.1
  have hlnn : l ≠ null := (hc.2.2.2.2.1 _ _ hnml).1
  have hres : resolve B r.nv.pgid' = some l := by
    unfold resolve
    split
    · rename_i h0
      have hpar : r.nv.parent' = null := by
        by_cases hp : r.nv.parent' = null
        · exact hp
        · obtain ⟨rp, hrp, hbr, -⟩ := hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
          rw [hc.2.2.2.2.2.2.1 h0 _ rp hrp] at hbr; cases hbr
      have hroot := hcl.2.2.2.2.2.2.2.2.2.2.2.2.1 hpar
      rw [hroot, if_neg hlnn]
    · exact hnml
  have hu : underPos W B B.ib.root' r.nv.pgid' := by
    by_cases h0 : B.ib.root' = W64 0
    · rw [h0, hcl.2.2.2.2.2.2.2.1 h0]; exact underPos.self _
    · exact under_chain W hwm bl B hc rk N hrk h0 (N + 1) l r (by omega) hrl
  refine ⟨hres, hu, ?_⟩
  have hka := kidsAt_node W B _ l r hres hrl
  rw [hleaf] at hka; simp only [if_true] at hka
  obtain ⟨w, hw, hwk⟩ := hk
  exact ⟨hka, _, keysAt_node W B _ l r hres hrl, List.mem_map.2 ⟨w, hw, hwk⟩⟩

/-- A leaf page under a page position holding an entry: its position, under the root. -/
theorem pos_page (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hr : bktRanked B) (l : Loc) (rl : NRec) (i : Nat) (w : WEntry)
    (hrl : B.ns !! l = some rl) (hbr : rl.nv.isLeaf' = false) (hwi : rl.ws[i]? = some w)
    (hnm : B.nm !! w.pgid = none) (p : Nat) (hown : ownHas W.pages (uint.nat w.pgid) p)
    (pg : List w8) (hpg : W.pages !! p = some pg) (hfl : pageFlags pg = leafPageFlag) (j : Nat)
    (hj : j < pageCount pg) :
    p < 2 ^ 64 ∧ resolve B (W64 (p : Int)) = none ∧ underPos W B B.ib.root' (W64 (p : Int)) ∧
      leafHas W B (W64 (p : Int)) (leafKey pg j) := by
  obtain ⟨rk, N, hrk⟩ := hr
  have hp64 : p < 2 ^ 64 := by
    have h1 := hv.2.2.2.1 p pg hpg
    have h2 := hv.2.1
    have : p ≤ p * W.ps := Nat.le_mul_of_pos_right p (by omega)
    omega
  have h0 : B.ib.root' ≠ W64 0 := by
    intro h0; rw [hc.2.2.2.2.2.2.1 h0 l rl hrl] at hbr; cases hbr
  have hpos : pagePosAt B l i w.pgid := ⟨rl, w, hrl, hbr, hwi, rfl, hnm⟩
  have hfree0 := hc.2.2.2.2.2.2.2.2.2 l i w.pgid hpos
  have hc64 : uint.nat w.pgid < 2 ^ 64 := uint_nat_lt' _
  have hfree : ∀ d, treeHas W.pages (uint.nat w.pgid) d → B.nm !! W64 (d : Int) = none :=
    hfree0
  have hul := under_chain W hwm bl B hc rk N hrk h0 (N + 1) l rl (by omega) hrl
  have hcl := hc.2.2.2.2.2.2.2.1 l rl hrl
  have hresl : resolve B rl.nv.pgid' = some l := by
    unfold resolve; rw [if_neg h0]; exact hcl.2.2.2.2.2.2.1
  have hka := kidsAt_node W B _ l rl hresl hrl
  rw [hbr] at hka; simp only [Bool.false_eq_true, if_false] at hka
  have huc : underPos W B B.ib.root' (W64 ((uint.nat w.pgid : Nat) : Int)) := by
    rw [w64_nat_eq]
    refine underPos_snoc W B _ _ _ i _ hul hka ?_
    rw [List.getElem?_map, hwi]; rfl
  have hud := under_pages W B h0 _ p hown hfree hc64
  have hres : resolve B (W64 (p : Int)) = none := by
    unfold resolve; rw [if_neg h0]
    exact hfree p (ownHas_tree' _ _ _ hown)
  have hwp := wpageAt_page W B (W64 (p : Int)) pg h0 (by rw [nat_w64_eq p hp64]; exact hpg)
  refine ⟨hp64, hres, underPos_trans W B _ _ _ huc hud, ?_, _, keysAt_page W B _ _ _ hres hwp, ?_⟩
  · have hka := kidsAt_page W B _ _ _ hres hwp
    rw [if_pos hfl, decide_eq_true hfl] at hka; exact hka
  · refine List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩
    unfold pageKey; rw [if_pos hfl]

/-- The leaf node `l` holds the nested bucket entry with key `k`. -/
def ownL (B : BRec) (l : Loc) (k : List w8) : Prop :=
  ∃ r w, B.ns !! l = some r ∧ r.nv.isLeaf' = true ∧ w ∈ r.ws ∧ w.key = k ∧ isBktFlag w.flags

/-- The branch node `l`'s page position `i` holds the nested bucket entry with key `k`. -/
def ownP (W : WView) (B : BRec) (l : Loc) (i : Nat) (k : List w8) : Prop :=
  ∃ r w p pg j, B.ns !! l = some r ∧ r.nv.isLeaf' = false ∧ r.ws[i]? = some w ∧
    B.nm !! w.pgid = none ∧ ownHas W.pages (uint.nat w.pgid) p ∧ W.pages !! p = some pg ∧
    pageFlags pg = leafPageFlag ∧ j < pageCount pg ∧ leafKey pg j = k ∧
    leafFlags pg j % 2 = bucketLeafFlag

/-- The node `l` (or one of its page positions) holds the nested bucket entry with key `k`. -/
def ownN (W : WView) (B : BRec) (l : Loc) (k : List w8) : Prop :=
  ownL B l k ∨ ∃ i, ownP W B l i k

theorem own_unique (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (k : List w8) :
    (∀ l1 l2, ownL B l1 k → ownL B l2 k → l1 = l2) ∧
    (∀ l1 l2 i, ownL B l1 k → ownP W B l2 i k → False) ∧
    (∀ l1 l2 i1 i2, ownP W B l1 i1 k → ownP W B l2 i2 k → l1 = l2 ∧ i1 = i2) := by
  have ht := tkp_root W hwm bl B bnd hv hc hk hr
  have hL : ∀ l, ownL B l k → ∃ e, resolve B e = some l ∧ underPos W B B.ib.root' e ∧
      leafHas W B e k := by
    rintro l ⟨r, w, hrl, hleaf, hw, hwk, -⟩
    obtain ⟨a, b, c⟩ := pos_leaf W hwm bl B hc hr l r hrl hleaf k ⟨w, hw, hwk⟩
    exact ⟨_, a, b, c⟩
  have hP : ∀ l i, ownP W B l i k → ∃ (p : Nat) (r : NRec) (w : WEntry), p < 2 ^ 64 ∧
      B.ns !! l = some r ∧ r.ws[i]? = some w ∧ pagePosAt B l i w.pgid ∧
      treeHas W.pages (uint.nat w.pgid) p ∧
      resolve B (W64 (p : Int)) = none ∧ underPos W B B.ib.root' (W64 (p : Int)) ∧
      leafHas W B (W64 (p : Int)) k := by
    rintro l i ⟨r, w, p, pg, j, hrl, hbr, hwi, hnm, hown, hpg, hfl, hj, hjk, -⟩
    obtain ⟨a, b, c, d⟩ := pos_page W hwm bl B hv hc hr l r i w hrl hbr hwi hnm p hown pg hpg hfl j hj
    rw [hjk] at d
    exact ⟨p, r, w, a, hrl, hwi, ⟨r, w, hrl, hbr, hwi, rfl, hnm⟩, ownHas_tree' _ _ _ hown, b, c, d⟩
  refine ⟨fun l1 l2 h1 h2 => ?_, fun l1 l2 i h1 h2 => ?_, fun l1 l2 i1 i2 h1 h2 => ?_⟩
  · obtain ⟨e1, r1, u1, a1⟩ := hL l1 h1
    obtain ⟨e2, r2, u2, a2⟩ := hL l2 h2
    have := leafHas_unique W B k _ _ _ ht e1 e2 u1 u2 a1 a2
    subst this; rw [r1] at r2; exact Option.some.inj r2
  · obtain ⟨e1, r1, u1, a1⟩ := hL l1 h1
    obtain ⟨p, -, -, -, -, -, -, -, r2, u2, a2⟩ := hP l2 i h2
    have := leafHas_unique W B k _ _ _ ht e1 _ u1 u2 a1 a2
    subst this; rw [r1] at r2; cases r2
  · obtain ⟨p1, ra, wa, p1l, hra, hwa, hpa, hta, r1, u1, a1⟩ := hP l1 i1 h1
    obtain ⟨p2, rb, wb, p2l, hrb, hwb, hpb, htb, r2, u2, a2⟩ := hP l2 i2 h2
    have he := leafHas_unique W B k _ _ _ ht _ _ u1 u2 a1 a2
    have hp : p1 = p2 := by
      have := congrArg (fun x : w64 => uint.nat x) he
      have e1 := nat_w64_eq p1 p1l
      have e2 := nat_w64_eq p2 p2l
      exact e1.symm.trans (this.trans e2)
    subst hp
    by_cases hne : l1 = l2 ∧ i1 = i2
    · exact hne
    exfalso
    have hne' : (l1, i1) ≠ (l2, i2) := by
      intro e; simp only [Prod.mk.injEq] at e; exact hne e
    exact hc.2.2.2.2.2.2.2.2.1 l1 i1 _ l2 i2 _ hpa hpb hne' p1 hta htb

end wherek

/-! ### A page position's tree: its pages but the opened buckets', and those -/

section split
variable [ext : FfiSyntax]

/-- A page of the tree under `c` is reached without the nested buckets `op` names, or through
one of them (an entry on a leaf page under `c`). -/
theorem treeHas_split (pages : GMap Nat (List w8)) (op : List w8 → Prop) :
    ∀ c d, treeHas pages c d → xHas pages op c d ∨
      ∃ p pg j, ownHas pages c p ∧ pages !! p = some pg ∧ pageFlags pg = leafPageFlag ∧
        j < pageCount pg ∧ leafFlags pg j % 2 = bucketLeafFlag ∧ op (leafKey pg j) ∧
        bucketHas pages (leafValue pg j) d := by
  intro c d h
  induction h using treeHas.rec
    (motive_2 := fun pg d _ => ∀ r, pages !! r = some pg → xHas pages op r d ∨
      ∃ p pg' j, ownHas pages r p ∧ pages !! p = some pg' ∧ pageFlags pg' = leafPageFlag ∧
        j < pageCount pg' ∧ leafFlags pg' j % 2 = bucketLeafFlag ∧ op (leafKey pg' j) ∧
        bucketHas pages (leafValue pg' j) d)
    (motive_3 := fun _ _ _ => True) with
  | root r pg hpg => exact Or.inl (xHas.root r pg hpg)
  | sub r pg id hpg _ ih => exact ih r hpg
  | child pg i id hb hi _ ih =>
    rename_i r hpg
    rcases ih with h | ⟨p, pg', j, ho, hp, hl, hj, hf, hop, hbk⟩
    · exact Or.inl (xHas.child r pg i id hpg hb hi h)
    · exact Or.inr ⟨p, pg', j, ownHas.child r pg i p hpg hb hi ho, hp, hl, hj, hf, hop, hbk⟩
  | bucket pg i id hl hi hf hbk _ =>
    rename_i r hpg
    by_cases hop : op (leafKey pg i)
    · exact Or.inr ⟨r, pg, i, ownHas.root r pg hpg, hpg, hl, hi, hf, hop, hbk⟩
    · exact Or.inl (xHas.bucket r pg i id hpg hl hi hf hop hbk)
  | file _ _ _ _ _ => trivial
  | inline _ _ _ _ _ => trivial

/-- An inline bucket's page reaches no page. -/
theorem inline_noHas (pages : GMap Nat (List w8)) (v : List w8) (hg : inlineGood (inlinePage v))
    (h0 : inBucketRoot v = 0) (d : Nat) (h : bucketHas pages v d) : False := by
  cases h with
  | file _ _ h1 _ => exact h1 h0
  | inline _ _ _ hp =>
    cases hp with
    | child _ i _ hb _ _ =>
      rw [hg.2.1] at hb; exact absurd hb (by unfold leafPageFlag branchPageFlag; decide)
    | bucket _ i _ _ hi hf _ =>
      rw [(hg.2.2.2.2 i hi).2] at hf; exact absurd hf (by unfold bucketLeafFlag; decide)

end split

section ptoks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- A page position's tokens (`xPages`) and the opened buckets' trees reached through it: its
tree's. -/
theorem pos_toks {K : Type} (γ : GName) (pages : GMap Nat (List w8)) (op : List w8 → Prop)
    (c : Nat) (Ks : List K) (P : K → Nat → Prop)
    (hcov : ∀ d, treeHas pages c d → xHas pages op c d ∨ ∃ k ∈ Ks, P k d) :
    pgToks (GF := GF) γ (xPages pages op c) ∗ ([∗list] k ∈ Ks, pgToks γ (pagesWith pages (P k))) ⊢
      pgToks γ (treePages pages c) := by
  show pgToks (GF := GF) γ (pagesWith pages (xHas pages op c)) ∗ _ ⊢
    pgToks γ (pagesWith pages (treeHas pages c))
  refine (sep_mono .rfl (pgToks_family γ pages P Ks)).trans ?_
  refine (pgToks_or γ pages _ _).trans ?_
  exact pgToks_mono γ pages _ _ (fun d h => hcov d h)

end ptoks

/-! ### An opened bucket's old tree, as the pages its entry reaches -/

section oldk
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The pages the tree of `B`'s nested bucket named `k` (in pages) reaches. -/
def kidPages (W : WView) (B : BRec) (k : List w8) (d : Nat) : Prop :=
  ∃ v, entryIn W B k v ∧ inBucketRoot v ≠ 0 ∧ treeHas W.pages (inBucketRoot v) d

theorem oldToks_root (γ : GName) (W : WView) (ib ib' : internal.common.InBucket)
    (h : ib.root' = ib'.root') : oldToks (GF := GF) γ W ib = oldToks γ W ib' := by
  unfold oldToks; rw [h]

/-- An opened bucket's old tree: the pages its entry reaches. -/
theorem kid_old_toks (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (k v : List w8) (hen : entryIn W B k v) :
    oldToks (GF := GF) γ W (ibOf v) ⊢ pgToks γ (pagesWith W.pages (kidPages W B k)) := by
  have hlt := inBucketRoot_lt v
  have hu : ∀ v', entryIn W B k v' → v' = v := fun v' h =>
    entryIn_unique W hwm bl B bnd hv hc hk hr k v' v h hen
  unfold oldToks ibOf
  simp only
  split
  · rename_i he
    have h0 : inBucketRoot v = 0 := by
      have := congrArg (fun x : w64 => uint.nat x) he
      have e1 := nat_w64_eq _ hlt
      exact e1.symm.trans (this.trans rfl)
    iintro _
    iapply pgToks_mono γ W.pages (fun _ => False) _ (fun d ⟨v', hv', hr', _⟩ => by
      rw [hu v' hv'] at hr'; exact hr' h0)
    iapply pgToks_none
  · rw [nat_w64_eq _ hlt]
    show pgToks (GF := GF) γ (pagesWith W.pages (treeHas W.pages (inBucketRoot v))) ⊢ _
    exact pgToks_mono γ W.pages _ _ (fun d ⟨v', hv', _, ht⟩ => by rw [hu v' hv'] at ht; exact ht)

end oldk

/-! ### The nodes as a tree (`kidsTree`), from their ranks -/

section ntree
variable [ext : FfiSyntax]

/-- `x` is `a` or below it (through the parent pointers). -/
inductive desc (ns : GMap Loc NRec) (a : Loc) : Loc → Prop
  | refl (r : NRec) : ns !! a = some r → desc ns a a
  | step (x : Loc) (rx : NRec) : ns !! x = some rx → rx.nv.parent' ≠ null →
      desc ns a rx.nv.parent' → desc ns a x

theorem desc_some (ns : GMap Loc NRec) (a x : Loc) (h : desc ns a x) : (ns !! x).isSome := by
  cases h with
  | refl r hr => rw [hr]; rfl
  | step _ rx hx _ _ => rw [hx]; rfl

theorem desc_rank (ns : GMap Loc NRec) (rk : Loc → Nat)
    (hrk : ∀ l r, ns !! l = some r → r.nv.parent' ≠ null → rk l < rk r.nv.parent') (a : Loc) :
    ∀ x, desc ns a x → rk x ≤ rk a := by
  intro x h
  induction h with
  | refl => exact Nat.le_refl _
  | step x rx hx hp _ ih => have := hrk x rx hx hp; omega

theorem desc_cmp (ns : GMap Loc NRec) (a : Loc) :
    ∀ x, desc ns a x → ∀ b, desc ns b x → desc ns a b ∨ desc ns b a := by
  intro x h
  induction h with
  | refl r hr => intro b h2; exact Or.inr h2
  | step x rx hx hp hd ih =>
    intro b h2
    cases h2 with
    | refl r' _ => exact Or.inl (desc.step x rx hx hp hd)
    | step _ rx' hx' _ hd' =>
      rw [hx] at hx'; cases hx'
      exact ih b hd'

theorem desc_trans (ns : GMap Loc NRec) (a c : Loc) (hac : desc ns a c) :
    ∀ x, desc ns c x → desc ns a x := by
  intro x h
  induction h with
  | refl => exact hac
  | step x rx hx hp _ ih => exact desc.step x rx hx hp ih

theorem desc_child (ns : GMap Loc NRec) (a : Loc) :
    ∀ x, desc ns a x → x = a ∨ ∃ c rc, ns !! c = some rc ∧ rc.nv.parent' = a ∧ desc ns c x := by
  intro x h
  induction h with
  | refl => exact Or.inl rfl
  | step x rx hx hp hd ih =>
    rcases ih with e | ⟨c, rc, hc, hcp, hcd⟩
    · exact Or.inr ⟨x, rx, hx, e, desc.refl rx hx⟩
    · exact Or.inr ⟨c, rc, hc, hcp, desc.step x rx hx hp hcd⟩

theorem forall2_mem_r {α β : Type} (R : α → β → Prop) :
    ∀ (xs : List α) (ys : List β), List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y := by
  intro xs ys h
  induction h with
  | nil => intro y hy; simp at hy
  | cons hr _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with e | e
    · subst e; exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, h⟩ := ih y e; exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

theorem forall2_mem_l {α β : Type} (R : α → β → Prop) :
    ∀ (xs : List α) (ys : List β), List.Forall₂ R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y := by
  intro xs ys h
  induction h with
  | nil => intro x hx; simp at hx
  | cons hr _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with e | e
    · subst e; exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, h⟩ := ih x e; exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem forall2_of {α β : Type} (R : α → β → Prop) :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ y, R x y) → ∃ ys, List.Forall₂ R xs ys := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨[], List.Forall₂.nil⟩
  | cons x xs ih =>
    intro h
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := ih (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    exact ⟨y :: ys, List.Forall₂.cons hy hys⟩

theorem forall2_mono {α β : Type} (R R' : α → β → Prop) (h : ∀ x y, R x y → R' x y) :
    ∀ (xs : List α) (ys : List β), List.Forall₂ R xs ys → List.Forall₂ R' xs ys := by
  intro xs ys hf
  induction hf with
  | nil => exact List.Forall₂.nil
  | cons hr _ ih => exact List.Forall₂.cons (h _ _ hr) ih

theorem flat_nodup (R : Loc → List Loc → Prop) :
    ∀ (cs : List Loc) (subs : List (List Loc)), List.Forall₂ R cs subs → cs.Nodup →
      (∀ c S, R c S → S.Nodup) →
      (∀ c1 c2 S1 S2, R c1 S1 → R c2 S2 → c1 ≠ c2 → ∀ x, x ∈ S1 → x ∈ S2 → False) →
      subs.flatten.Nodup := by
  intro cs subs h
  induction h with
  | nil => intro _ _ _; simp
  | cons hr hrest ih =>
    rename_i c S cs' subs'
    intro hnd hS hd
    rw [List.flatten_cons, List.nodup_append]
    refine ⟨hS _ _ hr, ih (List.nodup_cons.1 hnd).2 hS hd, fun a ha b hb e => ?_⟩
    subst e
    obtain ⟨S', hS', ha'⟩ := List.mem_flatten.1 hb
    obtain ⟨c', hc', hr'⟩ := forall2_mem_r R _ _ hrest S' hS'
    have hne : c ≠ c' := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hc')
    exact hd c c' S S' hr hr' hne a ha ha'

/-- The nodes from `l` down form a tree (`kidsTree`), its nodes those below `l`. -/
theorem kids_exists (ns : GMap Loc NRec) (rk : Loc → Nat)
    (hrk : ∀ l r, ns !! l = some r → r.nv.parent' ≠ null → rk l < rk r.nv.parent')
    (hcs : ∀ l r, ns !! l = some r → ∀ c ∈ r.cs, ∃ rc, ns !! c = some rc ∧ rc.nv.parent' = l)
    (hpar : ∀ l r, ns !! l = some r → r.nv.parent' ≠ null →
      ∃ rp, ns !! r.nv.parent' = some rp ∧ l ∈ rp.cs)
    (hnd : ∀ l r, ns !! l = some r → r.cs.Nodup) (hnn : ∀ l r, ns !! l = some r → l ≠ null) :
    ∀ n l r, rk l < n → ns !! l = some r → ∃ S, kidsTree ns l S ∧ ∀ x, x ∈ S ↔ desc ns l x := by
  intro n
  induction n with
  | zero => intro l r h; omega
  | succ n ih =>
    intro l r hlt hl
    have hlnn := hnn l r hl
    have hch : ∀ c ∈ r.cs, ∃ S, (∃ rc, ns !! c = some rc ∧ rc.nv.parent' = l) ∧
        kidsTree ns c S ∧ ∀ x, x ∈ S ↔ desc ns c x := by
      intro c hc
      obtain ⟨rc, hrc, hcp⟩ := hcs l r hl c hc
      have := hrk c rc hrc (by rw [hcp]; exact hlnn)
      rw [hcp] at this
      obtain ⟨S, h1, h2⟩ := ih c rc (by omega) hrc
      exact ⟨S, ⟨rc, hrc, hcp⟩, h1, h2⟩
    obtain ⟨subs, hsubs⟩ := forall2_of _ r.cs hch
    have hdl : ∀ c rc, ns !! c = some rc → rc.nv.parent' = l → desc ns l c := fun c rc hrc hcp =>
      desc.step c rc hrc (by rw [hcp]; exact hlnn) (by rw [hcp]; exact desc.refl r hl)
    have hlow : ∀ c rc, ns !! c = some rc → rc.nv.parent' = l → ¬ desc ns c l := by
      intro c rc hrc hcp hd
      have h1 := desc_rank ns rk hrk c l hd
      have h2 := hrk c rc hrc (by rw [hcp]; exact hlnn)
      rw [hcp] at h2; omega
    have hmem : ∀ x, x ∈ l :: subs.flatten ↔ desc ns l x := by
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.1 hx with e | e
        · subst e; exact desc.refl r hl
        · obtain ⟨S, hS, hxS⟩ := List.mem_flatten.1 e
          obtain ⟨c, -, ⟨rc, hrc, hcp⟩, -, hiff⟩ := forall2_mem_r _ _ _ hsubs S hS
          exact desc_trans ns l c (hdl c rc hrc hcp) x ((hiff x).1 hxS)
      · intro hd
        rcases desc_child ns l x hd with e | ⟨c, rc, hrc, hcp, hcd⟩
        · subst e; exact List.mem_cons_self
        · have hcl : c ∈ r.cs := by
            obtain ⟨rp, hrp, hc⟩ := hpar c rc hrc (by rw [hcp]; exact hlnn)
            rw [hcp, hl] at hrp; cases hrp; exact hc
          obtain ⟨S, hS, -, -, hiff⟩ := forall2_mem_l _ _ _ hsubs c hcl
          exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨S, hS, (hiff x).2 hcd⟩)
    refine ⟨l :: subs.flatten, kidsTree.mk l r subs hl
      (forall2_mono _ _ (fun _ _ h => h.2.1) _ _ hsubs) ?_, hmem⟩
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, flat_nodup _ r.cs subs hsubs (hnd l r hl)
      (fun c S h => kidsTree_nodup ns c S h.2.1) (fun c1 c2 S1 S2 h1 h2 hne x hx1 hx2 => ?_)⟩
    · obtain ⟨S, hS, hxS⟩ := List.mem_flatten.1 hx
      obtain ⟨c, -, ⟨rc, hrc, hcp⟩, -, hiff⟩ := forall2_mem_r _ _ _ hsubs S hS
      exact hlow c rc hrc hcp ((hiff l).1 hxS)
    · have d1 := (h1.2.2 x).1 hx1
      have d2 := (h2.2.2 x).1 hx2
      obtain ⟨r1, hr1, hp1⟩ := h1.1
      obtain ⟨r2, hr2, hp2⟩ := h2.1
      -- one is below the other; below a child of `l` other than itself is below `l`
      have key : ∀ a ra b rb, ns !! a = some ra → ra.nv.parent' = l → ns !! b = some rb →
          rb.nv.parent' = l → a ≠ b → desc ns a b → False := by
        intro a ra b rb hra hpa hrb hpb hab hd
        cases hd with
        | refl => exact hab rfl
        | step _ rb' hrb' _ hd' =>
          rw [hrb] at hrb'; cases hrb'
          rw [hpb] at hd'
          exact hlow a ra hra hpa hd'
      rcases desc_cmp ns c1 x d1 c2 d2 with h | h
      · exact key c1 r1 c2 r2 hr1 hp1 hr2 hp2 hne h
      · exact key c2 r2 c1 r1 hr2 hp2 hr1 hp1 (Ne.symm hne) h

end ntree

/-! ### The nodes' facts (`nodeU`) -/

section nfacts
variable [ext : FfiSyntax]

/-- The children of the branch `r` are all of the kind `kind` (leaves if `true`). -/
def kindP (W : WView) (B : BRec) (r : NRec) (kind : Bool) : Prop :=
  ∀ (i : Nat) (w : WEntry), r.ws[i]? = some w →
    (∀ l', B.nm !! w.pgid = some l' → ∃ r', B.ns !! l' = some r' ∧ r'.nv.isLeaf' = kind) ∧
    (B.nm !! w.pgid = none → ∃ pg, W.pages !! uint.nat w.pgid = some pg ∧
      decide (pageFlags pg = leafPageFlag) = kind)

open Classical in
/-- The kind of the node `l`'s children, as a page flag. -/
def kdOf (W : WView) (B : BRec) (l : Loc) : Nat :=
  if ∃ r, B.ns !! l = some r ∧ kindP W B r true then leafPageFlag else branchPageFlag

theorem kindP_unique (W : WView) (B : BRec) (r : NRec) (hn : 0 < r.ws.length) (k1 k2 : Bool)
    (h1 : kindP W B r k1) (h2 : kindP W B r k2) : k1 = k2 := by
  obtain ⟨w, hw⟩ : ∃ w, r.ws[0]? = some w := ⟨_, List.getElem?_eq_getElem hn⟩
  cases hnm : B.nm !! w.pgid with
  | some l' =>
    obtain ⟨r1, hr1, e1⟩ := (h1 0 w hw).1 l' hnm
    obtain ⟨r2, hr2, e2⟩ := (h2 0 w hw).1 l' hnm
    rw [hr1] at hr2; cases hr2; rw [← e1, ← e2]
  | none =>
    obtain ⟨p1, hp1, e1⟩ := (h1 0 w hw).2 hnm
    obtain ⟨p2, hp2, e2⟩ := (h2 0 w hw).2 hnm
    rw [hp1] at hp2; cases hp2; rw [← e1, ← e2]

theorem kdOf_eq (W : WView) (B : BRec) (l : Loc) (r : NRec) (hr : B.ns !! l = some r)
    (hn : 0 < r.ws.length) (kind : Bool) (hk : kindP W B r kind) :
    kdOf W B l = if kind then leafPageFlag else branchPageFlag := by
  unfold kdOf
  cases kind with
  | false =>
    have : ¬ ∃ r', B.ns !! l = some r' ∧ kindP W B r' true := by
      rintro ⟨r', hr', hk'⟩; rw [hr] at hr'; cases hr'
      exact absurd (kindP_unique W B r hn _ _ hk hk') (by decide)
    rw [if_neg this]; rfl
  | true =>
    rw [if_pos (⟨r, hr, hk⟩ : ∃ r', B.ns !! l = some r' ∧ kindP W B r' true)]; rfl

theorem bndIn_refl' (a : Option (List w8) × Option (List w8)) : bndIn a a :=
  ⟨fun y hy => ⟨y, hy, goStringLt_irrefl_r y⟩, fun y hy => ⟨y, hy, goStringLt_irrefl_r y⟩⟩

/-- The kind of a branch's children, from its keys. -/
theorem kindP_of (W : WView) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (l : Loc) (r : NRec) (hk : nodeKeys W B bnd l r) (hbr : r.nv.isLeaf' = false) :
    ∃ kind, kindP W B r kind := by
  obtain ⟨-, kind, hkind⟩ := hk.2.2.2.1 hbr
  refine ⟨kind, fun i w hw => ⟨(hkind i w hw).1, fun hn => ?_⟩⟩
  obtain ⟨pg, hpg, -, hd, -⟩ := (hkind i w hw).2 hn
  exact ⟨pg, hpg, hd⟩

/-- A clean node with exact keys is unspilled-ready (`nodeU`). -/
theorem nodeU_of (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (l : Loc) (r : NRec) (hr : B.ns !! l = some r) :
    nodeU W bl B bnd (kdOf W B) l r := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩ :=
    hc.2.2.2.2.2.2.2.1 l r hr
  have nk := hk.2.2 l r hr
  have hlnn : l ≠ null := (hc.2.2.2.2.1 _ _ c7).1
  refine ⟨c1, c6, c2, c3, fun w hw => ⟨c4 w hw, nk.1 w hw⟩, c5, c10, fun hp => ?_, fun hleaf => ?_,
    fun hbr => ?_⟩
  · by_cases h0 : B.ib.root' = W64 0
    · exact absurd (c8 h0) hp
    · cases c9 h0 with
      | page _ pg _ hpg _ _ => exact ⟨pg, hpg, _, c9 h0⟩
  · cases hcs : r.cs with
    | nil => rfl
    | cons c cs =>
      exfalso
      obtain ⟨rc, hrc, hcp⟩ := c16 c (by rw [hcs]; exact List.mem_cons_self)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, d14, -⟩ := hc.2.2.2.2.2.2.2.1 c rc hrc
      obtain ⟨rp, hrp, hbr, -⟩ := d14 (by rw [hcp]; exact hlnn)
      rw [hcp, hr] at hrp; cases hrp
      rw [hleaf] at hbr; cases hbr
  · obtain ⟨-, hnd, hall⟩ := c12 hbr
    obtain ⟨h2, -⟩ := nk.2.2.2.1 hbr
    obtain ⟨kind, hkind⟩ := kindP_of W B bnd l r nk hbr
    have hkd := kdOf_eq W B l r hr (by omega) kind hkind
    refine ⟨hnd, h2, c15, fun i w c hi hm => ?_, fun c hc' => ?_⟩
    · obtain ⟨-, rc, hrc, hpg⟩ := hc.2.2.2.2.1 _ _ hm
      have hwm : w ∈ r.ws := List.mem_of_getElem? hi
      obtain ⟨-, hpar, -⟩ := hall w hwm
      obtain ⟨r', hr', hp'⟩ := hpar c hm
      rw [hrc] at hr'; cases hr'
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, d14, -⟩ := hc.2.2.2.2.2.2.2.1 c rc hrc
      have hcnull : rc.nv.parent' ≠ null := by rw [hp']; exact hlnn
      obtain ⟨hkey', rp, i', w', hrp, hw', hpg', hkey, hbnd⟩ := (hk.2.2 c rc hrc).2.2.1 hcnull
      rw [hp', hr] at hrp; cases hrp
      have hi' := pgid_idx_eq r.ws hnd i i' w w' hi hw' (hpg'.trans hpg)
      subst hi'
      rw [hi] at hw'; cases hw'
      obtain ⟨rp2, hrp2, -, hcm, -⟩ := d14 hcnull
      rw [hp', hr] at hrp2; cases hrp2
      obtain ⟨r'', hr'', hl''⟩ := (hkind _ w hi).1 c hm
      rw [hrc] at hr''; cases hr''
      refine ⟨rc, hrc, hp', hpg, hkey.symm, hkey', hcm, ?_, ?_⟩
      · rw [hkd, hl'']
      · rw [hbnd, hp']; exact bndIn_refl' _
    · obtain ⟨rc, hrc, hcp⟩ := c16 c hc'
      have hcnull : rc.nv.parent' ≠ null := by rw [hcp]; exact hlnn
      obtain ⟨-, rp, i, w, hrp, hw, hpg, -, -⟩ := (hk.2.2 c rc hrc).2.2.1 hcnull
      rw [hcp, hr] at hrp; cases hrp
      obtain ⟨-, -, -, -, -, -, d7, -⟩ := hc.2.2.2.2.2.2.2.1 c rc hrc
      exact ⟨i, w, hw, by rw [hpg]; exact d7⟩

/-- Every node is below the root node. -/
theorem desc_root (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (rk : Loc → Nat) (N : Nat)
    (hrk : ∀ l r, B.ns !! l = some r → rk l ≤ N ∧ (r.nv.parent' ≠ null → rk l < rk r.nv.parent')) :
    ∀ n l r, N - rk l < n → B.ns !! l = some r → desc B.ns B.bv.rootNode' l := by
  intro n
  induction n with
  | zero => intro l r h; omega
  | succ n ih =>
    intro l r hlt hr
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, c13, c14, -⟩ := hc.2.2.2.2.2.2.2.1 l r hr
    by_cases hp : r.nv.parent' = null
    · rw [c13 hp]; exact desc.refl r hr
    · obtain ⟨rp, hrp, -⟩ := c14 hp
      have h1 := (hrk l r hr).2 hp
      have h2 := (hrk _ rp hrp).1
      exact desc.step l r hr hp (ih _ rp (by omega) hrp)

end nfacts

/-! ### Lists of nodes and entries -/

section lists
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- A map whose keys are the list `S`, as a list over `S`. -/
theorem bigSepM_list {K V : Type} [DecidableEq K] (Φ : K → V → IProp GF) :
    ∀ (S : List K) (m : GMap K V), S.Nodup → (∀ k, (m !! k).isSome ↔ k ∈ S) →
      ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗list] k ∈ S, ∃ x, ⌜m !! k = some x⌝ ∗ Φ k x := by
  intro S
  induction S with
  | nil =>
    intro m _ h
    refine (bigSepM_none Φ m (fun k => ?_)).1.trans (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    cases hk : m !! k with
    | none => rfl
    | some x => exact absurd ((h k).1 (by rw [hk]; rfl)) (by simp)
  | cons k S ih =>
    intro m hnd h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((h k).2 (List.mem_cons_self))
    refine (BigSepM.bigSepM_delete (M := GMap K) (Φ := Φ)
      (show Std.get? m k = some x from hx)).1.trans ?_
    refine BIBase.Entails.trans ?_ (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    refine sep_mono ?_ ?_
    · iintro H; iexists x; iframe H; ipureintro; exact hx
    · refine (ih _ (List.nodup_cons.1 hnd).2 (fun k' => ?_)).trans
        (BigSepL.bigSepL_mono (fun {j k'} hk' => ?_))
      · show (GMap.delete k m !! k').isSome ↔ k' ∈ S
        by_cases e : k' = k
        · subst e
          rw [GMap.lookup_delete]
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          exact (List.nodup_cons.1 hnd).1
        · rw [GMap.lookup_delete_ne _ (Ne.symm e), h k']
          simp [e]
      · iintro ⟨%y, %hy, H⟩
        iexists y; iframe H; ipureintro
        have hne : k' ≠ k := by
          intro e; subst e
          change (GMap.delete k' m) !! k' = some y at hy
          rw [GMap.lookup_delete] at hy; cases hy
        change (GMap.delete k m) !! k' = some y at hy
        rwa [GMap.lookup_delete_ne _ (Ne.symm hne)] at hy

/-- A list over the indices of `ws`, as a list over `ws`. -/
theorem bigSepL_range_ix {A : Type} :
    ∀ (ws : List A) (Φ : Nat → IProp GF),
      ([∗list] i ∈ List.range ws.length, Φ i) ⊣⊢ [∗list] i ↦ _w ∈ ws, Φ i := by
  intro ws
  induction ws with
  | nil => intro Φ; simp
  | cons w ws ih =>
    intro Φ
    rw [List.length_cons, List.range_succ_eq_map]
    refine (BigSepL.bigSepL_cons (PROP := IProp GF)).trans ?_
    refine BiEntails.trans ?_ (BigSepL.bigSepL_cons (PROP := IProp GF)).symm
    refine sep_congr .rfl ?_
    rw [BigSepL.bigSepL_map]
    exact ih (fun i => Φ (i + 1))

end lists

/-! ### Each opened bucket's owner: the node holding its entry -/

section owner
variable [ext : FfiSyntax]

open Classical in
/-- The node holding the nested bucket entry with key `k` (`ownN`). -/
noncomputable def ownerOf (W : WView) (B : BRec) (k : List w8) : Loc :=
  if h : ∃ l, ownN W B l k then Classical.choose h else null

open Classical in
/-- The page position of `l` holding the nested bucket entry with key `k` (`ownP`). -/
noncomputable def idxOf (W : WView) (B : BRec) (l : Loc) (k : List w8) : Nat :=
  if h : ∃ i, ownP W B l i k then Classical.choose h else 0

theorem ownN_unique (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (k : List w8) (l1 l2 : Loc)
    (h1 : ownN W B l1 k) (h2 : ownN W B l2 k) : l1 = l2 := by
  obtain ⟨u1, u2, u3⟩ := own_unique W hwm bl B bnd hv hc hk hr k
  rcases h1 with a | ⟨i, a⟩ <;> rcases h2 with b | ⟨j, b⟩
  · exact u1 _ _ a b
  · exact (u2 _ _ _ a b).elim
  · exact (u2 _ _ _ b a).elim
  · exact (u3 _ _ _ _ a b).1

theorem ownerOf_eq (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (k : List w8) (l : Loc) (h : ownN W B l k) :
    ownerOf W B k = l := by
  have hex : ∃ l, ownN W B l k := ⟨l, h⟩
  unfold ownerOf; rw [dif_pos hex]
  exact ownN_unique W hwm bl B bnd hv hc hk hr k _ _ (Classical.choose_spec hex) h

theorem idxOf_eq (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (l : Loc) (i : Nat) (k : List w8)
    (h : ownP W B l i k) : idxOf W B l k = i := by
  have hex : ∃ i, ownP W B l i k := ⟨i, h⟩
  unfold idxOf; rw [dif_pos hex]
  exact ((own_unique W hwm bl B bnd hv hc hk hr k).2.2 _ _ _ _ (Classical.choose_spec hex) h).2

/-- An opened bucket's entry has an owner (the bucket having a materialized root). -/
theorem own_of_bm (W : WView) (T : WTx) (B : BRec) (hn : bktNested W T B)
    (hrn : B.bv.rootNode' ≠ null) (k : List w8) (c : Loc) (hkc : B.bm !! k = some c) :
    ∃ l, ownN W B l k := by
  obtain ⟨C, v, -, hen, -⟩ := hn k c hkc
  rcases hen with ⟨l, r, w, hr, hleaf, hw, hkey, hbkt, -⟩ |
    ⟨c', p, pg, i, hpos, hown, hpg, hfl, hi, hkey, hbf, -⟩
  · exact ⟨l, Or.inl ⟨r, w, hr, hleaf, hw, hkey, hbkt⟩⟩
  · rcases hpos with ⟨hrn', -, -⟩ | ⟨l, j, ⟨rl, w, hrl, hbr, hwj, hpj, hnm⟩, hlt⟩
    · exact absurd hrn' hrn
    · refine ⟨l, Or.inr ⟨j, rl, w, p, pg, i, hrl, hbr, hwj, by rw [hpj]; exact hnm, ?_, hpg, hfl,
        hi, hkey, hbf⟩⟩
      rw [hpj, nat_w64_eq c' hlt]; exact hown

theorem ownN_some (W : WView) (B : BRec) (l : Loc) (k : List w8) (h : ownN W B l k) :
    (B.ns !! l).isSome := by
  rcases h with ⟨r, -, hr, -⟩ | ⟨-, r, -, -, -, -, hr, -⟩
  · rw [hr]; rfl
  · rw [hr]; rfl

end owner

/-! ### An entry's written value -/

section wval
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A nested bucket value's tree's tokens (none for an inline one). -/
def rootToks (γ : GName) (W : WView) (v : List w8) : IProp GF :=
  if inBucketRoot v = 0 then emp else pgToks γ (treePages W.pages (inBucketRoot v))

theorem oldToks_ibOf (γ : GName) (W : WView) (v : List w8) :
    oldToks (GF := GF) γ W (ibOf v) ⊣⊢ rootToks γ W v := by
  have hlt := inBucketRoot_lt v
  unfold oldToks ibOf rootToks
  simp only
  by_cases h0 : inBucketRoot v = 0
  · rw [if_pos h0, if_pos (by rw [h0]; rfl)]; exact .rfl
  · have hne : W64 ((inBucketRoot v : Nat) : Int) ≠ W64 0 := by
      intro e
      have := congrArg (fun x : w64 => uint.nat x) e
      exact h0 ((nat_w64_eq _ hlt).symm.trans (this.trans rfl))
    rw [if_neg h0, if_neg hne, nat_w64_eq _ hlt]; exact .rfl

/-- A nested bucket value's old tree: its written value. -/
theorem rootToks_wbkt (γ : GName) (W : WView) (hwm : Nat) (v : List w8) (hv : viewOK W)
    (hb : bvalOK W.pages hwm v) (hk : inBucketRoot v ≠ 0 → treeKeys W.pages (inBucketRoot v) none none)
    (hh : hwm ≤ 2 ^ 64) (pht : Nat → Nat) (hph : pageHts W.pages pht)
    (P : GMap Nat (List w8)) (hP : W.pages ⊆ P) :
    rootToks (GF := GF) γ W v ⊢ wbktQP γ P v := by
  have h16 : 16 ≤ v.length := by
    cases hb.1 with
    | file _ h _ _ => exact h
    | inline _ h _ _ _ => exact h
  unfold rootToks wbktQP
  by_cases h0 : inBucketRoot v = 0
  · rw [if_pos h0, if_pos h0]
    iintro _
    isplitr
    · ipureintro; exact h16
    · ipureintro; exact hb.2 h0
  · rw [if_neg h0, if_neg h0]
    have hw : treeWF W.pages hwm (inBucketRoot v) := by
      cases hb.1 with
      | file _ _ _ h => exact h
      | inline _ _ h _ _ => exact absurd h h0
    iintro H
    isplitr
    · ipureintro; exact h16
    iexists treePages W.pages (inBucketRoot v)
    isplitr
    · ipureintro
      exact map_subseteq_trans (treePages_sub W.pages _) hP
    ihave Hq := wtreeQ_old γ W.pages hwm _ none none hw hv.2.2.2.2 (hk h0) hh pht hph $$ H
    icases Hq with ⟨Hq, -⟩
    iexact Hq

end wval

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The result of the opened bucket named `k` of `B`: its entry's value `v` now, and either
its written value (a changed bucket: its entry in a materialized leaf), or its old tree. -/
def kidRes (γ : GName) (W : WView) (T : WTx) (B : BRec) (k : List w8) : IProp GF :=
  iprop(∃ v, ⌜entryIn W B k v ∧ 16 ≤ v.length⌝ ∗
    ((⌜∃ l r w, B.ns !! l = some r ∧ r.nv.isLeaf' = true ∧ w ∈ r.ws ∧ w.key = k ∧
        w.value = v⌝ ∗ wbktQP γ (spillPages W T) v) ∨
     (⌜bvalOK W.pages (uint.nat T.mv.pgid') v ∧
        (inBucketRoot v ≠ 0 → treeKeys W.pages (inBucketRoot v) none none)⌝ ∗
      oldToks γ W (ibOf v))))

/-- An opened bucket's result, for its entry's value `v` in a leaf: its written value. -/
theorem kid_wbkt (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (k v : List w8) (hen : entryIn W B k v)
    (pht : Nat → Nat) (hph : pageHts W.pages pht) :
    kidRes (GF := GF) γ W T B k ⊢ wbktQP γ (spillPages W T) v := by
  unfold kidRes
  iintro ⟨%v', %Hv', Hr⟩
  have he := entryIn_unique W hwm bl B bnd hv hc hk hr k v' v Hv'.1 hen
  subst he
  icases Hr with (⟨-, Hw⟩ | ⟨%Hbk, Ho⟩)
  · iexact Hw
  · ihave Ho := (oldToks_ibOf γ W v').1 $$ Ho
    iapply rootToks_wbkt γ W (uint.nat T.mv.pgid') v' hv Hbk.1 Hbk.2
      (by have := (T.mv.pgid').isLt; unfold uint.nat; omega) pht hph (spillPages W T)
      (GMap.map_union_subseteq_l _ _)
    iexact Ho

/-- An opened bucket's result, for its entry on a page position: its old tree. -/
theorem kid_posS (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (l : Loc) (i : Nat) (k : List w8)
    (hown : ownP W B l i k) :
    kidRes (GF := GF) γ W T B k ⊢ pgToks γ (pagesWith W.pages (kidPages W B k)) := by
  unfold kidRes
  iintro ⟨%v, %Hv, Hr⟩
  icases Hr with (⟨%Hl, -⟩ | ⟨-, Ho⟩)
  · exfalso
    obtain ⟨l', r', w', hr', hleaf', hw', hk', -⟩ := Hl
    have ht := tkp_root W hwm bl B bnd hv hc hk hr
    obtain ⟨a1, u1, h1⟩ := pos_leaf W hwm bl B hc hr l' r' hr' hleaf' k ⟨w', hw', hk'⟩
    obtain ⟨rl, w, p, pg, j, hrl, hbr, hwi, hnm, hown', hpg, hfl, hj, hjk, -⟩ := hown
    obtain ⟨-, a2, u2, h2⟩ := pos_page W hwm bl B hv hc hr l rl i w hrl hbr hwi hnm p hown' pg hpg hfl j hj
    rw [hjk] at h2
    have := leafHas_unique W B k _ _ _ ht _ _ u1 u2 h1 h2
    rw [this, a2] at a1; cases a1
  · iapply kid_old_toks γ W hwm bl B bnd hv hc hk hr k v Hv.1
    iexact Ho

theorem nodup_of_wsSorted (ws : List WEntry) (hs : wsSorted ws) : (ws.map WEntry.key).Nodup := by
  have hk : keysSorted (ws.map WEntry.key) := keysSorted_fn (keysFn_ws ws) hs
  unfold List.Nodup
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij e
  have h1 : (ws.map WEntry.key)[i]? = some (ws.map WEntry.key)[i] := List.getElem?_eq_getElem hi
  have h2 : (ws.map WEntry.key)[j]? = some (ws.map WEntry.key)[i] := by
    rw [List.getElem?_eq_getElem hj, e]
  exact goStringLt_irrefl_r _ (hk i j _ _ hij h1 h2)

open Classical in
/-- A leaf's entries' tokens and its opened buckets' results: its entries' written values. -/
theorem node_leaf (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (hn : bktNested W T B)
    (hrn : B.bv.rootNode' ≠ null) (hh : hwm ≤ 2 ^ 64) (pht : Nat → Nat)
    (hph : pageHts W.pages pht) (l : Loc) (r : NRec)
    (hrl : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true) :
    ([∗list] w ∈ r.ws, if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
        pgToks γ (treePages W.pages (inBucketRoot w.value)) else emp) ∗
      ([∗map] k ↦ _c ∈ GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm,
        kidRes (GF := GF) γ W T B k) ⊢
      [∗list] i ↦ w ∈ r.ws, (if w.flags &&& W32 1 = W32 0 then emp
        else wbktQP γ (spillPages W T) w.value) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩ :=
    hc.2.2.2.2.2.2.2.1 l r hrl
  have nk := hk.2.2 l r hrl
  let Pf : WEntry → Bool := fun w => decide (isBktFlag w.flags ∧ opened B w.key)
  have hdom : ∀ k, (GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm !! k).isSome ↔
      k ∈ (r.ws.filter Pf).map WEntry.key := by
    intro k
    rw [GMap.lookup_filter]
    constructor
    · intro h
      cases hb : B.bm !! k with
      | none => rw [hb] at h; cases h
      | some c =>
        rw [hb] at h
        have ho : ownerOf W B k = l := by
          by_cases hne : ownerOf W B k = l
          · exact hne
          · simp [Option.filter, hne] at h
        obtain ⟨l', hl'⟩ := own_of_bm W T B hn hrn k c hb
        have := ownerOf_eq W hwm bl B bnd hv hc hk hr k l' hl'
        rw [ho] at this; subst this
        rcases hl' with ⟨r', w, hr', -, hw, hwk, hwb⟩ | ⟨i, r', -, -, -, -, hr', hbr, -⟩
        · rw [hrl] at hr'; cases hr'
          refine List.mem_map.2 ⟨w, List.mem_filter.2 ⟨hw, ?_⟩, hwk⟩
          simp only [Pf, decide_eq_true_eq]
          exact ⟨hwb, by unfold opened; rw [hwk, hb]; rfl⟩
        · rw [hrl] at hr'; cases hr'; rw [hleaf] at hbr; cases hbr
    · intro h
      obtain ⟨w, hw, hwk⟩ := List.mem_map.1 h
      obtain ⟨hw, hp⟩ := List.mem_filter.1 hw
      simp only [Pf, decide_eq_true_eq] at hp
      obtain ⟨hb, hop⟩ := hp
      obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.1 hop
      rw [hwk] at hc'
      rw [hc']
      have := ownerOf_eq W hwm bl B bnd hv hc hk hr k l (Or.inl ⟨r, w, hrl, hleaf, hw, hwk, hb⟩)
      simp [Option.filter, this]
  have hnd : ((r.ws.filter Pf).map WEntry.key).Nodup :=
    List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) (nodup_of_wsSorted r.ws c3)
  iintro ⟨Hn, Hm⟩
  ihave Hm := (bigSepM_keys (fun k => kidRes (GF := GF) γ W T B k) _ _ hnd hdom).1 $$ Hm
  ihave Hm := (bigSepL_filter_keys (fun k => kidRes (GF := GF) γ W T B k) WEntry.key Pf r.ws).1 $$ Hm
  ihave H := (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).2 $$ [Hn Hm]
  · iframe
  iapply (BigSepL.bigSepL_mono (fun {i w} hi => ?_)) $$ H
  have hw : w ∈ r.ws := List.mem_of_getElem? hi
  by_cases hb : isBktFlag w.flags
  · have hf : ¬ (w.flags &&& W32 1 = W32 0) := hb
    rw [if_neg hf]
    obtain ⟨hbv, -⟩ := c11 hleaf w hw hb
    have hkv := nk.2.2.2.2.2 hleaf w hw hb
    by_cases hop : opened B w.key
    · have hpf : Pf w = true := by simp only [Pf, decide_eq_true_eq]; exact ⟨hb, hop⟩
      have hno : ¬ (isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key) :=
        fun h => h.2.2 hop
      simp only [hpf, ite_true]
      rw [if_neg hno]
      iintro ⟨H, -⟩
      iapply kid_wbkt γ W T hwm bl B bnd hv hc hk hr w.key w.value
        (Or.inl ⟨l, r, w, hrl, hleaf, hw, rfl, hb, rfl⟩) pht hph
      iexact H
    · have hpf : Pf w = false := by simp only [Pf, decide_eq_false_iff_not]; exact fun h => hop h.2
      simp only [hpf, Bool.false_eq_true, ite_false]
      iintro ⟨-, H⟩
      have hop' : (B.bm !! w.key).isSome = false := by
        unfold opened at hop; simpa using hop
      iapply rootToks_wbkt γ W hwm w.value hv (hbv hop') (fun h0 => hkv h0 hop) hh pht hph (spillPages W T)
        (GMap.map_union_subseteq_l _ _)
      unfold rootToks
      by_cases h0 : inBucketRoot w.value = 0
      · rw [if_pos h0]; iclear H; iempintro
      · have hyes : isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key := ⟨hb, h0, hop⟩
        rw [if_neg h0]
        rw [if_pos hyes] at *
        iexact H
  · have hf : w.flags &&& W32 1 = W32 0 := by unfold isBktFlag at hb; exact Classical.not_not.1 hb
    have hno : ¬ (isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key) :=
      fun h => hb h.1
    have hpf : Pf w = false := by simp only [Pf, decide_eq_false_iff_not]; exact fun h => hb h.1
    rw [if_pos hf]
    simp only [hpf, Bool.false_eq_true, ite_false]
    rw [if_neg hno]
    iintro ⟨-, -⟩
    iempintro

open Classical in
/-- A branch's page positions' tokens and its opened buckets' results (on them): its entries'
written trees. -/
theorem node_branch (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (hn : bktNested W T B)
    (hrn : B.bv.rootNode' ≠ null) (hh : hwm ≤ 2 ^ 64) (pht : Nat → Nat)
    (hph : pageHts W.pages pht) (ht : Nat) (l : Loc) (r : NRec)
    (hrl : B.ns !! l = some r) (hbr : r.nv.isLeaf' = false)
    (hpos : ∀ w ∈ r.ws, B.nm !! w.pgid = none → pht (uint.nat w.pgid) + 1 = ht) :
    ([∗list] w ∈ r.ws, if B.nm !! w.pgid = none then
        pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid)) else emp) ∗
      ([∗map] k ↦ _c ∈ GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm,
        kidRes (GF := GF) γ W T B k) ⊢
      [∗list] i ↦ w ∈ r.ws, entRes γ (spillPages W T) B (bnd l).2 false (kdOf W B l) (ht - 1) r.ws i w := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩ :=
    hc.2.2.2.2.2.2.2.1 l r hrl
  have nk := hk.2.2 l r hrl
  obtain ⟨hlen2, kind, hkind⟩ := nk.2.2.2.1 hbr
  obtain ⟨kind', hkind'⟩ := kindP_of W B bnd l r nk hbr
  have hkd := kdOf_eq W B l r hrl (by omega) kind' hkind'
  have hkk : kind' = kind := kindP_unique W B r (by omega) _ _ hkind'
    (fun i w hw => ⟨(hkind i w hw).1, fun hn => by
      obtain ⟨pg, hpg, -, hd, -⟩ := (hkind i w hw).2 hn; exact ⟨pg, hpg, hd⟩⟩)
  subst hkk
  -- the opened buckets this node holds, by page position
  have hMown : ∀ k x, GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm !! k = some x →
      ownP W B l (idxOf W B l k) k := by
    intro k x hk'
    rw [GMap.lookup_filter] at hk'
    cases hb : B.bm !! k with
    | none => rw [hb] at hk'; cases hk'
    | some c =>
      rw [hb] at hk'
      have ho : ownerOf W B k = l := by
        by_cases hne : ownerOf W B k = l
        · exact hne
        · simp [Option.filter, hne] at hk'
      obtain ⟨l', hl'⟩ := own_of_bm W T B hn hrn k c hb
      have := ownerOf_eq W hwm bl B bnd hv hc hk hr k l' hl'
      rw [ho] at this; subst this
      rcases hl' with ⟨r', -, hr', hleaf', -⟩ | ⟨i, hi⟩
      · rw [hrl] at hr'; cases hr'; rw [hbr] at hleaf'; cases hleaf'
      · rw [idxOf_eq W hwm bl B bnd hv hc hk hr _ i k hi]; exact hi
  have hrange : ∀ k x, GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm !! k = some x →
      idxOf W B l k ∈ List.range r.ws.length := by
    intro k x hk'
    obtain ⟨r', w, -, -, -, hr', -, hwi, -⟩ := hMown k x hk'
    rw [hrl] at hr'; cases hr'
    exact List.mem_range.2 (List.getElem?_eq_some_iff.1 hwi).1
  iintro ⟨Hn, Hm⟩
  ihave Hm := bigSepM_partition (fun k (_ : Loc) => kidRes (GF := GF) γ W T B k) (idxOf W B l)
    (List.range r.ws.length) _ List.nodup_range hrange $$ Hm
  ihave Hm := (bigSepL_range_ix r.ws (fun i => iprop([∗map] k ↦ _x ∈ GMap.filter
    (fun k _ => decide (idxOf W B l k = i))
      (GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm), kidRes (GF := GF) γ W T B k))).1 $$ Hm
  ihave H := (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)
    (Φ := fun _ (w : WEntry) => if B.nm !! w.pgid = none then
        pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid)) else emp)
    (Ψ := fun i (_ : WEntry) => iprop([∗map] k ↦ _x ∈ GMap.filter (fun k _ => decide (idxOf W B l k = i))
      (GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm), kidRes (GF := GF) γ W T B k))).2
    $$ [Hn Hm]
  · iframe
  iapply (BigSepL.bigSepL_mono (fun {i w} hi => ?_)) $$ H
  have hw : w ∈ r.ws := List.mem_of_getElem? hi
  -- the keys of position `i`
  have hMi : ∀ k x, GMap.filter (fun k _ => decide (idxOf W B l k = i))
      (GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm) !! k = some x → ownP W B l i k := by
    intro k x hk'
    rw [GMap.lookup_filter] at hk'
    cases hb : GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm !! k with
    | none => rw [hb] at hk'; cases hk'
    | some y =>
      rw [hb] at hk'
      have hix : idxOf W B l k = i := by
        by_cases hne : idxOf W B l k = i
        · exact hne
        · simp [Option.filter, hne] at hk'
      have := hMown k y hb
      rw [hix] at this; exact this
  unfold entRes
  simp only [Bool.false_eq_true, ite_false]
  by_cases hnm : B.nm !! w.pgid = none
  · rw [if_pos hnm, if_pos hnm]
    iintro ⟨Hx, Hk⟩
    ihave Hk := (BigSepM.bigSepM_mono (fun {k x} hk' =>
      kid_posS (GF := GF) γ W T hwm bl B bnd hv hc hk hr l i k (hMi k x hk'))) $$ Hk
    ihave Hk := (bigSepM_keys (fun k => pgToks (GF := GF) γ (pagesWith W.pages (kidPages W B k)))
      _ _ (GMap.nodup_dom_list _) (fun k => (GMap.mem_dom_list _ k).symm)).1 $$ Hk
    have hcov : ∀ d, treeHas W.pages (uint.nat w.pgid) d → xHas W.pages (opened B) (uint.nat w.pgid) d ∨
        ∃ k ∈ (GMap.filter (fun k _ => decide (idxOf W B l k = i))
          (GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm)).domList, kidPages W B k d := by
      intro d hd
      rcases treeHas_split W.pages (opened B) _ d hd with h | ⟨p, pg, j, ho, hp, hl, hj, hf, hop, hbk⟩
      · exact Or.inl h
      · have hown : ownP W B l i (leafKey pg j) := ⟨r, w, p, pg, j, hrl, hbr, hi, hnm, ho, hp, hl, hj, rfl, hf⟩
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 hop
        have hoeq := ownerOf_eq W hwm bl B bnd hv hc hk hr _ l (Or.inr ⟨i, hown⟩)
        have hieq := idxOf_eq W hwm bl B bnd hv hc hk hr l i _ hown
        refine Or.inr ⟨leafKey pg j, (GMap.mem_dom_list _ _).2 ?_, leafValue pg j, ?_, ?_⟩
        · rw [GMap.lookup_filter, GMap.lookup_filter, hc']
          simp [Option.filter, hoeq, hieq]
        · have h64 : uint.nat w.pgid < 2 ^ 64 := uint_nat_lt' _
          refine Or.inr ⟨uint.nat w.pgid, p, pg, j, Or.inr ⟨l, i, ⟨r, w, hrl, hbr, hi, ?_, ?_⟩, h64⟩,
            ho, hp, hl, hj, rfl, hf, rfl⟩
          · rw [w64_nat_eq]
          · rw [w64_nat_eq]; exact hnm
        · have hg := ((hv.2.2.2.2.1 p pg hp).1 hl j hj).2 hf
          cases hbk with
          | file _ _ h1 h2 => exact ⟨h1, h2⟩
          | inline _ _ h1 h2 =>
            exact (inline_noHas W.pages _ (hg h1) h1 d (bucketHas.inline _ _ h1 h2)).elim
    ihave Ht := pos_toks γ W.pages (opened B) (uint.nat w.pgid) _ (kidPages W B) hcov $$ [Hx Hk]
    · iframe
    obtain ⟨-, -, htw⟩ := (c12 hbr).2.2 w hw
    have htw := htw hnm
    obtain ⟨pg, hpg, hcnt, hdk, hpk, htk⟩ := (hkind i w hi).2 hnm
    have htk' := treeKeys_first W.pages hwm _ pg _ _ htw htk hpg hcnt
    rw [hpk] at htk'
    ihave Ht := wtreeQ_old γ W.pages hwm (uint.nat w.pgid) (some w.key)
      (entryBnd (bnd l) r.ws i).2 htw hv.2.2.2.2 htk' hh pht hph $$ Ht
    icases Ht with ⟨Ht, %hq⟩
    iexists treePages W.pages (uint.nat w.pgid), pg, (entryBnd (bnd l) r.ws i).2
    iframe Ht
    ipureintro
    refine ⟨map_subseteq_trans (treePages_sub W.pages _) (GMap.map_union_subseteq_l _ _), ?_,
      hcnt, ?_, hpk, hiLe_refl _, ?_⟩
    · show (GMap.filter _ W.pages) !! _ = _
      rw [GMap.lookup_filter, hpg]
      simp [Option.filter, treeHas.root _ pg hpg]
    · rw [hkd]
      cases kind' with
      | true => simp only [ite_true]; exact of_decide_eq_true hdk
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have hnl : pageFlags pg ≠ leafPageFlag := of_decide_eq_false hdk
        cases htw with
        | page _ pg' _ hpg' _ hpt =>
          rw [hpg] at hpg'; cases hpg'
          cases hpt with
          | leaf _ _ hl _ _ => exact absurd hl hnl
          | branch _ _ hb _ _ => exact hb
    · have := hpos w hw hnm
      rw [show ht - 1 = pht (uint.nat w.pgid) by omega]
      exact hq
  · rw [if_neg hnm, if_neg hnm]
    iintro ⟨-, Hk⟩
    iapply (bigSepM_none _ _ (fun k => ?_)).1 $$ Hk
    cases hk' : (GMap.filter (fun k _ => decide (idxOf W B l k = i))
        (GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm)) !! k with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨r', w', -, -, -, hr', -, hwi', hnm', -⟩ := hMi k x hk'
      rw [hrl] at hr'; cases hr'
      rw [hi] at hwi'; cases hwi'
      exact hnm hnm'

open Classical in
/-- A node's tokens and its opened buckets' results: what it holds for `node.spill`. -/
theorem node_ready (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) (hn : bktNested W T B)
    (hrn : B.bv.rootNode' ≠ null) (hh : hwm ≤ 2 ^ 64) (pht : Nat → Nat)
    (hph : pageHts W.pages pht) (ht : Nat) (l : Loc) (r : NRec)
    (hrl : B.ns !! l = some r)
    (hpos : r.nv.isLeaf' = false → ∀ w ∈ r.ws, B.nm !! w.pgid = none → pht (uint.nat w.pgid) + 1 = ht) :
    nodeToks γ W B r ∗
      ([∗map] k ↦ _c ∈ GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm,
        kidRes (GF := GF) γ W T B k) ⊢
      rtoks γ (spillPages W T) B (bnd l) (kdOf W B l) (ht - 1) r := by
  have hu := nodeU_of W hwm bl B bnd hc hk l r hrl
  unfold nodeToks rtoks
  have hpage : (if r.nv.pgid' = W64 0 then emp else
      pgToks (GF := GF) γ (GMap.filter (fun id _ => decide (id = uint.nat r.nv.pgid')) W.pages)) ⊢
      (if r.nv.pgid' = W64 0 then emp else (uint.nat r.nv.pgid' ↪[γ] () : IProp GF)) := by
    by_cases hp0 : r.nv.pgid' = W64 0
    · rw [if_pos hp0, if_pos hp0]
    · rw [if_neg hp0, if_neg hp0]
      obtain ⟨pg, hpg, -⟩ := hu.2.2.2.2.2.2.2.1 hp0
      exact (pgToks_single γ W.pages _ pg hpg).1
  cases hleaf : r.nv.isLeaf'
  · simp only [Bool.false_eq_true, ite_false]
    iintro ⟨⟨Hp, He⟩, Hk⟩
    isplitl [Hp]
    · iapply hpage; iexact Hp
    · iapply node_branch γ W T hwm bl B bnd hv hc hk hr hn hrn hh pht hph ht l r hrl hleaf (hpos hleaf)
      iframe
  · simp only [ite_true]
    iintro ⟨⟨Hp, He⟩, Hk⟩
    isplitl [Hp]
    · iapply hpage; iexact Hp
    · unfold entRes
      simp only [ite_true]
      iapply node_leaf γ W T hwm bl B bnd hv hc hk hr hn hrn hh pht hph l r hrl hleaf
      iframe

/-- A bucket with a materialized root, its opened buckets done: its nodes' facts and tokens, as
`node.spill` takes them. -/
theorem ready_of_shape (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (K : Loc → Bool) (bnd0 : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hk : bktKeysB W B bnd0)
    (hr : bktRanked B) (hn : bktNested W T B) (hl : leafPg0 B) (hrn : B.bv.rootNode' ≠ null)
    (hK : ∀ l r, B.ns !! l = some r → K l = false ∧ r.nv.unbalanced' = false)
    (hwmv : W.hwm ≤ hwm) (hh : hwm ≤ 2 ^ 64) (hht : rblHt W B) :
    bktToks γ W B ∗ ([∗map] k ↦ _c ∈ B.bm, kidRes γ W T B k) ⊢
      ∃ (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (ht : Loc → Nat)
        (S : List Loc),
        ⌜bnd B.bv.rootNode' = (none, none) ∧ subU W bl B bnd kd K B.bv.rootNode' S ∧
          (∀ l, (B.ns !! l).isSome ↔ l ∈ S) ∧ nodeHts B ht⌝ ∗
        [∗list] l ∈ S, ∃ r, ⌜B.ns !! l = some r⌝ ∗
          rtoks γ (spillPages W T) B (bnd l) (kd l) (ht l - 1) r := by
  obtain ⟨ht, pht, hph, hnode⟩ := hht
  obtain ⟨rk, N, hrk⟩ := hr
  have hrk' : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → rk l < rk r.nv.parent' :=
    fun l r h hp => (hrk l r h).2 hp
  have hnmr := hc.2.2.2.1 hrn
  obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 _ _ hnmr
  have hcl := hc.2.2.2.2.2.2.2.1
  obtain ⟨S, hkt, hS⟩ := kids_exists B.ns rk hrk'
    (fun l r h => (hcl l r h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun l r h hp => by
      obtain ⟨rp, hrp, -, hm, -⟩ := (hcl l r h).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
      exact ⟨rp, hrp, hm⟩)
    (fun l r h => (hcl l r h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun l r h => (hc.2.2.2.2.1 _ _ (hcl l r h).2.2.2.2.2.2.1).1)
    (N + 1) _ r0 (by have := (hrk _ r0 hr0).1; omega) hr0
  have hall : ∀ l, (B.ns !! l).isSome ↔ l ∈ S := by
    intro l
    constructor
    · intro h
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
      exact (hS l).2 (desc_root W hwm bl B hc rk N hrk (N + 1) l r (by omega) hr)
    · intro h; exact desc_some _ _ _ ((hS l).1 h)
  have hbnd : bnd0 B.bv.rootNode' = (none, none) := (hk.2.2 _ r0 hr0).2.1 (hk.2.1 r0 hr0)
  have hnd : S.Nodup := kidsTree_nodup _ _ _ hkt
  have hrr : bktRanked B := ⟨rk, N, hrk⟩
  unfold bktToks
  rw [if_neg hrn]
  iintro ⟨Hb, Hm⟩
  ihave Hb := bigSepM_list (fun _ r => nodeToks (GF := GF) γ W B r) S B.ns hnd hall $$ Hb
  ihave Hm := bigSepM_partition (fun k (_ : Loc) => kidRes (GF := GF) γ W T B k) (ownerOf W B) S B.bm
    hnd (fun k x hkx => by
      obtain ⟨l, hl⟩ := own_of_bm W T B hn hrn k x hkx
      rw [ownerOf_eq W hwm bl B bnd0 hv hc hk hrr k l hl]
      exact (hall l).1 (ownN_some W B l k hl)) $$ Hm
  have hnh : nodeHts B ht := by
    intro l r hr _
    refine ⟨fun hlf => (hnode l r hr).1 hlf, fun hbr => ⟨?_, fun w hw c hc' => (hnode l r hr).2 hbr w hw |>.1 c hc'⟩⟩
    obtain ⟨hpos, -⟩ := ((hcl l r hr).2.2.2.2.2.2.2.2.2.2.2.1 hbr)
    obtain ⟨w, hw⟩ : ∃ w, w ∈ r.ws := ⟨r.ws[0]'hpos, List.getElem_mem hpos⟩
    by_cases hm : B.nm !! w.pgid = none
    · have := ((hnode l r hr).2 hbr w hw).2 hm; omega
    · obtain ⟨c, hc'⟩ := Option.ne_none_iff_exists'.1 hm
      have := ((hnode l r hr).2 hbr w hw).1 c hc'; omega
  iexists bnd0, kdOf W B, ht, S
  isplitr
  · ipureintro
    refine ⟨hbnd, ⟨hkt, fun x hx => ?_⟩, hall, hnh⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((hall x).2 hx)
    exact ⟨(hK x r hr).1, r, hr, nodeU_of W hwm bl B bnd0 hc hk x r hr⟩
  ihave H := (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)
    (Φ := fun _ l => iprop(∃ r, ⌜B.ns !! l = some r⌝ ∗ nodeToks (GF := GF) γ W B r))
    (Ψ := fun _ l => iprop([∗map] k ↦ _x ∈ GMap.filter (fun k _ => decide (ownerOf W B k = l)) B.bm,
      kidRes (GF := GF) γ W T B k))).2 $$ [Hb Hm]
  · iframe
  iapply (BigSepL.bigSepL_mono (fun {j l} _ => ?_)) $$ H
  iintro ⟨⟨%r, %hrl, Hn⟩, Hk⟩
  iexists r
  isplitr
  · ipureintro; exact hrl
  iapply node_ready γ W T hwm bl B bnd0 hv hc hk hrr hn hrn hh pht hph (ht l) l r hrl
    (fun hbr w hw hm => ((hnode l r hrl).2 hbr w hw).2 hm)
  iframe

/-- A bucket's pages without a materialized root: its root's pages but the opened buckets', and
those. -/
theorem old_core (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hrn : B.bv.rootNode' = null) (h0 : B.ib.root' ≠ W64 0) :
    pgToks (GF := GF) γ (xPages W.pages (opened B) (uint.nat B.ib.root')) ∗
      ([∗map] k ↦ _c ∈ B.bm, pgToks γ (pagesWith W.pages (kidPages W B k))) ⊢
      pgToks γ (treePages W.pages (uint.nat B.ib.root')) := by
  refine (sep_mono .rfl (bigSepM_keys (fun k => pgToks (GF := GF) γ (pagesWith W.pages (kidPages W B k)))
    B.bm.domList B.bm (GMap.nodup_dom_list _) (fun k => (GMap.mem_dom_list _ k).symm)).1).trans ?_
  refine pos_toks γ W.pages (opened B) _ B.bm.domList (kidPages W B) (fun d hd => ?_)
  rcases treeHas_split W.pages (opened B) _ d hd with h | ⟨p, pg, j, ho, hp, hl, hj, hf, hop, hbk⟩
  · exact Or.inl h
  · refine Or.inr ⟨leafKey pg j, (GMap.mem_dom_list _ _).2 hop, leafValue pg j, ?_, ?_⟩
    · exact Or.inr ⟨_, p, pg, j, Or.inl ⟨hrn, h0, rfl⟩, ho, hp, hl, hj, rfl, hf, rfl⟩
    · have hg := ((hv.2.2.2.2.1 p pg hp).1 hl j hj).2 hf
      cases hbk with
      | file _ _ h1 h2 => exact ⟨h1, h2⟩
      | inline _ _ h1 h2 =>
        exact (inline_noHas W.pages _ (hg h1) h1 d (bucketHas.inline _ _ h1 h2)).elim

/-- A bucket with no materialized root, its opened buckets unchanged: its old tree. -/
theorem old_of_shape (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd0 : Loc → Option (List w8) × Option (List w8))
    (hv : viewOK W) (hc : bktClean W hwm bl B) (hn : bktNested W T B)
    (hk : bktKeysB W B bnd0) (hr : bktRanked B) (hrn : B.bv.rootNode' = null) :
    bktToks γ W B ∗ ([∗map] k ↦ c ∈ B.bm, ∃ C, ⌜T.bs !! c = some C⌝ ∗ oldToks γ W C.ib) ⊢
      oldToks γ W B.ib := by
  unfold bktToks
  rw [if_pos hrn]
  by_cases h0 : B.ib.root' = W64 0
  · unfold oldToks
    rw [if_pos h0, if_pos h0]
    iintro ⟨_, _⟩
    iempintro
  · unfold oldToks
    rw [if_neg h0, if_neg h0]
    iintro ⟨Hx, Hm⟩
    iapply old_core γ W hwm bl B hv hc hrn h0
    iframe Hx
    iapply (BigSepM.bigSepM_mono (fun {k cl} hkc => ?_)) $$ Hm
    obtain ⟨C, v, hC, hen, -, -, hroot, -⟩ := hn k cl hkc
    iintro ⟨%C', %HC', Ho⟩
    rw [hC] at HC'; cases HC'
    rw [hroot]
    iapply kid_old_toks γ W hwm bl B bnd0 hv hc hk hr k v hen
    unfold oldToks
    iexact Ho

/-- `old_of_shape`, from the opened buckets' results (`kidRes`): none is changed (no node). -/
theorem old_of_kids (γ : GName) (W : WView) (T : WTx) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd0 : Loc → Option (List w8) × Option (List w8))
    (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd0) (hr : bktRanked B) (hrn : B.bv.rootNode' = null) :
    bktToks γ W B ∗ ([∗map] k ↦ _c ∈ B.bm, kidRes γ W T B k) ⊢ oldToks γ W B.ib := by
  unfold bktToks
  rw [if_pos hrn]
  by_cases h0 : B.ib.root' = W64 0
  · unfold oldToks
    rw [if_pos h0, if_pos h0]
    iintro ⟨_, _⟩
    iempintro
  · unfold oldToks
    rw [if_neg h0, if_neg h0]
    iintro ⟨Hx, Hm⟩
    iapply old_core γ W hwm bl B hv hc hrn h0
    iframe Hx
    iapply (BigSepM.bigSepM_mono (fun {k cl} _ => ?_)) $$ Hm
    unfold kidRes
    iintro ⟨%v, %Hv, Hr⟩
    icases Hr with (⟨%Hl, -⟩ | ⟨-, Ho⟩)
    · obtain ⟨l, r, -, hl, -⟩ := Hl
      rw [(hc.2.2.1 hrn).1] at hl; cases hl
    · iapply kid_old_toks γ W hwm bl B bnd0 hv hc hk hr k v Hv.1
      unfold oldToks
      iexact Ho

end own

end bbolt
end EtcdGrove
end Perennial
