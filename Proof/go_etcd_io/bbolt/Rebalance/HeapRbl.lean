/-
The writer's heap reshaped (U8b, `node.rebalance`, `notes/bbolt-proof-plan.md`): the objects at a
list of distinct locations taken out of `wtxHeap` (with the transaction's fields and the root
bucket's `FillPercent`), and put back as the objects of another record `X'` that agrees with `X`
everywhere else (its objects and liveness outside the list, its view). Every heap step of
`node.rebalance` (the start, a removal, the root collapse, a merge, a node going dead) is one.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.RblX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A map with the keys of a list deleted. -/
def delL {V : Type} : List Loc → GMap Loc V → GMap Loc V
  | [], M => M
  | a :: L, M => delL L (Iris.Std.delete M a)

omit [GooseExts] in
theorem delL_lookup {V : Type} (L : List Loc) (M : GMap Loc V) (k : Loc) :
    (delL L M) !! k = if k ∈ L then none else M !! k := by
  induction L generalizing M with
  | nil => simp [delL]
  | cons a L ih =>
    simp only [delL]
    rw [ih]
    show (if k ∈ L then none else (GMap.delete a M) !! k) = _
    by_cases hk : k = a
    · subst hk; simp
    · rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
      simp [hk]

omit [GooseExts] in
theorem delL_eq {V : Type} (L : List Loc) (M M' : GMap Loc V)
    (h : ∀ k, k ∉ L → M' !! k = M !! k) : delL L M' = delL L M := by
  apply GMap.ext
  intro k
  show (delL L M') !! k = (delL L M) !! k
  rw [delL_lookup, delL_lookup]
  split
  · rfl
  · exact h k ‹_›

omit hos [GooseSemantics] [GooseInterp] go_gctx in
/-- A big separating conjunction over a map: the entries at a list of distinct keys, and the
rest. -/
theorem bigSepM_delL {Φ : Loc → WObj → IProp GF} (L : List Loc) (M : GMap Loc WObj)
    (os : Loc → WObj) (hnd : L.Nodup) (ho : ∀ l ∈ L, M !! l = some (os l)) :
    ([∗map] l ↦ o ∈ M, Φ l o) ⊣⊢ ([∗list] l ∈ L, Φ l (os l)) ∗ [∗map] l ↦ o ∈ delL L M, Φ l o := by
  induction L generalizing M with
  | nil =>
    simp only [delL]
    exact emp_sep.symm
  | cons a L ih =>
    simp only [List.nodup_cons] at hnd
    have ha : Iris.Std.get? M a = some (os a) := ho a List.mem_cons_self
    have ho' : ∀ l ∈ L, (Iris.Std.delete M a : GMap Loc WObj) !! l = some (os l) := by
      intro l hl
      have hne : l ≠ a := fun h => hnd.1 (h ▸ hl)
      show (GMap.delete a M) !! l = _
      rw [GMap.lookup_delete_ne _ (Ne.symm hne)]
      exact ho l (List.mem_cons_of_mem _ hl)
    refine (BigSepM.bigSepM_delete (M := GMap Loc) ha).trans ?_
    refine (sep_congr .rfl (ih _ hnd.2 ho')).trans ?_
    simp only [delL]
    exact sep_assoc.symm

omit hos in
/-- **The heap reshaped**: the objects at the distinct locations `L` (the transaction's fields
and the root bucket's `FillPercent` too) out of `X`'s heap, and back as `X'`'s, when `X'` has
`X`'s view and agrees with `X` outside `L` (objects and liveness). -/
theorem wtxHeap_reshape (tx : Loc) (dq : DFrac) (X X' : WX) (L : List Loc) (os os' : Loc → WObj)
    (hnd : L.Nodup) (ho : ∀ l ∈ L, X.t.objs !! l = some (os l))
    (ho' : ∀ l ∈ L, X'.t.objs !! l = some (os' l)) (hv : X'.v = X.v)
    (hout : ∀ k, k ∉ L → X'.t.objs !! k = X.t.objs !! k ∧ (k ∈ X'.live ↔ k ∈ X.live)) :
    wtxHeap (GF := GF) tx dq X ⊢
      ([∗list] l ∈ L, objOwn X.v l dq (decide (l ∈ X.live)) (os l)) ∗ txFields tx dq X ∗
      rootFill tx dq ∗
      (⌜heapOK (GF := GF) tx X'⌝ -∗ ([∗list] l ∈ L, objOwn X.v l dq (decide (l ∈ X'.live)) (os' l)) -∗
        txFields tx dq X' -∗ rootFill tx dq -∗ wtxHeap tx dq X') := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hrf, Hm⟩
  icases (bigSepM_delL (Φ := fun l o => objOwn (GF := GF) X.v l dq (decide (l ∈ X.live)) o)
    L X.t.objs os hnd ho).1 $$ Hm with ⟨HL, Hm⟩
  iframe HL Hf Hrf
  iintro %Hok' HL Hf Hrf
  iframe Hf Hrf
  isplitr
  · ipureintro; exact Hok'
  rw [hv]
  iapply (bigSepM_delL (Φ := fun l o => objOwn (GF := GF) X.v l dq (decide (l ∈ X'.live)) o)
    L X'.t.objs os' hnd ho').2
  iframe HL
  rw [delL_eq L X.t.objs X'.t.objs (fun k hk => (hout k hk).1)]
  iapply (BigSepM.bigSepM_mono ?_) $$ Hm
  intro k o hk
  have hk' : (delL L X.t.objs) !! k = some o := hk
  rw [delL_lookup] at hk'
  split at hk'
  · cases hk'
  · rename_i hkL
    rw [show decide (k ∈ X'.live) = decide (k ∈ X.live) from decide_eq_decide.2 (hout k hkL).2]

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **Disjoint objects kept** when the buckets stay and each bucket's nodes are some of its
nodes before. -/
theorem objsDisj_sub (T T' : WTx) (hd : objsDisj T)
    (hdom : ∀ bl, (T'.bs !! bl).isSome = (T.bs !! bl).isSome)
    (hsub : ∀ bl B B' k, T.bs !! bl = some B → T'.bs !! bl = some B' → (B'.ns !! k).isSome →
      (B.ns !! k).isSome) :
    objsDisj T' := by
  have hget : ∀ bl B', T'.bs !! bl = some B' → ∃ B, T.bs !! bl = some B := by
    intro bl B' h
    have := hdom bl; rw [h] at this
    exact Option.isSome_iff_exists.1 this.symm
  intro bl B' hb' k hk
  obtain ⟨B, hb⟩ := hget bl B' hb'
  have hk0 := hsub bl B B' k hb hb' hk
  obtain ⟨h1, h2⟩ := hd bl B hb k hk0
  refine ⟨?_, ?_⟩
  · have := hdom k; rw [h1] at this
    cases h : T'.bs !! k with
    | none => rfl
    | some _ => rw [h] at this; cases this
  · intro bl'' C' hc' hne
    obtain ⟨C, hc⟩ := hget bl'' C' hc'
    have := h2 bl'' C hc hne
    cases h : C'.ns !! k with
    | none => rfl
    | some _ =>
      have := hsub bl'' C C' k hc hc' (by rw [h]; rfl)
      rw [‹C.ns !! k = none›] at this; cases this

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The objects agree outside `L`** when the buckets and their nodes (and the dead objects)
agree outside `L`. -/
theorem objs_agree (T T' : WTx) (L : List Loc) (hd : objsDisj T) (hd' : objsDisj T')
    (hdom : ∀ bl, (T'.bs !! bl).isSome = (T.bs !! bl).isSome)
    (hbs : ∀ bl, bl ∉ L → T'.bs !! bl = T.bs !! bl)
    (hns : ∀ bl B B' k, T.bs !! bl = some B → T'.bs !! bl = some B' → k ∉ L →
      B'.ns !! k = B.ns !! k)
    (hdead : ∀ k, k ∉ L → T'.dead !! k = T.dead !! k) :
    ∀ k, k ∉ L → T'.objs !! k = T.objs !! k := by
  intro k hk
  have hget : ∀ bl B, T.bs !! bl = some B → ∃ B', T'.bs !! bl = some B' := by
    intro bl B h
    have := hdom bl; rw [h] at this
    exact Option.isSome_iff_exists.1 this
  cases hkb : T.bs !! k with
  | some B =>
    rw [objs_bkt T k B hd hkb, objs_bkt T' k B hd' (by rw [hbs k hk]; exact hkb)]
  | none =>
    by_cases hex : ∃ bl B r, T.bs !! bl = some B ∧ B.ns !! k = some r
    · obtain ⟨bl, B, r, hb, hr⟩ := hex
      obtain ⟨B', hb'⟩ := hget bl B hb
      rw [objs_node T bl B k r hd hb hr,
        objs_node T' bl B' k r hd' hb' (by rw [hns bl B B' k hb hb' hk]; exact hr)]
    · have hno : ∀ bl B, T.bs !! bl = some B → k ≠ bl ∧ B.ns !! k = none := by
        intro bl B hb
        refine ⟨fun he => (by rw [he, hb] at hkb; cases hkb), ?_⟩
        cases h : B.ns !! k with
        | none => rfl
        | some r => exact absurd ⟨bl, B, r, hb, h⟩ hex
      rw [objs_other T k hno, objs_other T' k ?_, hdead k hk]
      intro bl B' hb'
      obtain ⟨B, hb⟩ : ∃ B, T.bs !! bl = some B := by
        have := hdom bl; rw [hb'] at this
        exact Option.isSome_iff_exists.1 this.symm
      refine ⟨(hno bl B hb).1, ?_⟩
      rw [hns bl B B' k hb hb' hk]; exact (hno bl B hb).2

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- A bucket's node under `rblX` is not its own parent (`rblAcyc`). -/
theorem parentNe_of_rblX (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) (hI : rblX X fl dbl dfc) :
    ∀ bl B n r, X.t.bs !! bl = some B → B.ns !! n = some r → r.nv.parent' ≠ n := by
  intro bl B n r hb hr he
  obtain ⟨-, -, ⟨ht, hh⟩, -⟩ := (hI.2.1 bl B hb).1
  have hpn : r.nv.parent' ≠ null := by
    intro h0
    have hc := (hI.2.1 bl B hb).1.1
    have hnm := (hc.2.2.2.2.2.2.2.1 n r hr).2.2.2.2.2.2.2.1
    exact (hc.2.2.2.2.1 _ _ hnm).1 (he.symm.trans h0)
  have := hh n r hr hpn; rw [he] at this; omega

omit hos [GooseSemantics] in
/-- The heap's facts for a reshaped record: the root, disjoint objects, the buckets' `tx`
fields, no node its own parent, and the registry's nodes still objects. -/
theorem heapOK_of (tx : Loc) (X X' : WX) (hok : heapOK (GF := GF) tx X) (hrl : X'.rl = X.rl)
    (hd : objsDisj X'.t)
    (htx : ∀ bl B', X'.t.bs !! bl = some B' → ∃ B, X.t.bs !! bl = some B ∧ B'.bv.tx' = B.bv.tx')
    (hpar : ∀ bl B n r, X'.t.bs !! bl = some B → B.ns !! n = some r → r.nv.parent' ≠ n)
    (hnl : X'.nloc = X.nloc)
    (hobj : ∀ k, (X.t.objs !! k).isSome → (X'.t.objs !! k).isSome) :
    heapOK (GF := GF) tx X' := by
  obtain ⟨h1, -, h3, -, h5⟩ := hok
  refine ⟨hrl.trans h1, hd, ?_, hpar, ?_⟩
  · intro bl B' hb'
    obtain ⟨B, hb, he⟩ := htx bl B' hb'
    rw [he]; exact h3 bl B hb
  · intro k y hk
    rw [hnl] at hk
    exact hobj k (h5 k y hk)

omit hos in
/-- The transaction's fields depend only on its struct, meta copy and page cache. -/
theorem txFields_congr (tx : Loc) (dq : DFrac) (X X' : WX) (h1 : X'.t.t = X.t.t)
    (h2 : X'.t.mv = X.t.mv) (h3 : X'.t.pm = X.t.pm) (h4 : X'.t.bufs = X.t.bufs) :
    txFields (GF := GF) tx dq X' = txFields tx dq X := by
  unfold txFields; rw [h1, h2, h3, h4]

end heap

end bbolt
end EtcdGrove
end Perennial
