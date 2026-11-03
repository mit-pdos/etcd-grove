/-
Heap lemmas for the Linux file extension's specs: deleting a cell of the non-atomic heap, and
reshaping the heap at a list of cells owned whole (`heap_reshape`), which every step that
renders the mapped cells uses.
-/
module

public import Perennial.GooseLang.Lifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.Std ProofMode
open goose_heap

section na_heap
open Iris.Algebra CMRA HeapView
variable {L V : Type} [DecidableEq L] {GF : BundledGFunctors} [hG : NaHeapGS L V GF]
variable {LK : Type} (tls : LK → LockState)

theorem toNaHeap_delete (σ : GMap L (LK × V)) (l : L) :
    toNaHeap tls (GMap.delete l σ) = Std.PartialMap.delete (toNaHeap tls σ) l := by
  apply GMap.ext; intro k
  show (toNaHeap tls (GMap.delete l σ)).lookup k = (GMap.delete l (toNaHeap tls σ)).lookup k
  simp only [toNaHeap, GMap.lookup_fmap]
  show Option.map _ ((GMap.delete l σ) !! k) = (GMap.delete l (toNaHeap tls σ)) !! k
  simp only [GMap.lookup_delete_iff]
  split
  · rfl
  · rfl

theorem na_heap_delete (σ : GMap L (LK × V)) (l : L) (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l (.own 1) v ==∗
      naHeapCtx tls (GMap.delete l σ) := by
  unfold naHeapCtx naHeapPointsto naHeapPointstoSt
  have hupd : Auth (H := GMap L) (.own 1) (toNaHeap tls σ) •
        Frag (H := GMap L) l (.own 1)
          ((toLockStateR (RSt 0), toAgree (DiscreteO.mk v)) : NaHeapCmra V) ~~>
      Auth (H := GMap L) (.own 1) (toNaHeap tls (GMap.delete l σ)) := by
    rw [toNaHeap_delete]
    exact update_one_delete
  iintro H1 H2
  iapply (iOwn_update hupd)
  iapply iOwn_op.2
  iframe

end na_heap

section reshape
variable [GooseExts] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

/-- The whole points-to of the cell `l` of the heap `h`, if it has one. -/
def fullPt (h : GMap Loc (NonAtomic val)) (l : Loc) : IProp GF :=
  match h !! l with
  | some x => heapPointsto l (.own 1) x.2
  | none => iprop(emp)

/-- `fullPt` of every cell of `T`. -/
def fullPts (h : GMap Loc (NonAtomic val)) : List Loc → IProp GF
  | [] => iprop(emp)
  | l :: T => iprop(fullPt h l ∗ fullPts h T)

theorem fullPts_congr {h h' : GMap Loc (NonAtomic val)} :
    ∀ {T : List Loc}, (∀ k ∈ T, h !! k = h' !! k) → fullPts (GF := GF) h T = fullPts h' T
  | [], _ => rfl
  | l :: T, H => by
    simp only [fullPts, fullPt]
    rw [H l (List.mem_cons_self), fullPts_congr (fun k hk => H k (List.mem_cons_of_mem _ hk))]

/-- One cell: from its whole points-to in `h0` to its whole points-to in `h0` with the cell
set as in `h'`. -/
theorem fullPt_step (h0 h' : GMap Loc (NonAtomic val)) (l : Loc)
    (hmode : ∀ x, h' !! l = some x → x.1 = Reading 0)
    (haddr : (h' !! l).isSome → 0 < l.addr ∧ l.addr < maxAddr) :
    naHeapCtx tls h0 ∗ fullPt (GF := GF) h0 l ⊢ |==>
      (naHeapCtx tls (match h' !! l with | some x => <[l := x]> h0 | none => GMap.delete l h0) ∗
        fullPt (match h' !! l with | some x => <[l := x]> h0 | none => GMap.delete l h0) l) := by
  unfold fullPt
  cases h0l : h0 !! l with
  | some x0 =>
    cases h'l : h' !! l with
    | some x =>
      obtain ⟨m, v⟩ := x
      have hm := hmode _ h'l; simp only at hm; subst hm
      simp only [GMap.lookup_insert]
      iintro ⟨Hσ, Hl⟩
      icases heapPointsto_na_acc l (.own 1) _ $$ Hl with ⟨Hl, Hrest⟩
      imod na_heap_write tls h0 l (Reading 0) x0.2 v rfl $$ Hσ Hl with ⟨Hσ, Hl⟩
      imodintro
      iframe Hσ
      iapply Hrest $$ Hl
    | none =>
      simp only [GMap.lookup_delete]
      iintro ⟨Hσ, Hl⟩
      icases heapPointsto_na_acc l (.own 1) _ $$ Hl with ⟨Hl, -⟩
      imod na_heap_delete tls h0 l x0.2 $$ Hσ Hl with Hσ
      imodintro
      iframe Hσ
  | none =>
    cases h'l : h' !! l with
    | some x =>
      obtain ⟨m, v⟩ := x
      have hm := hmode _ h'l; simp only at hm; subst hm
      have ha := haddr (by simp [h'l])
      simp only [GMap.lookup_insert]
      iintro ⟨Hσ, -⟩
      imod na_heap_alloc tls h0 l v (Reading 0) h0l rfl $$ Hσ with ⟨Hσ, Hl⟩
      imodintro
      iframe Hσ
      iapply na_pointsto_to_heap l _ _ ha $$ Hl
    | none =>
      have : GMap.delete l h0 = h0 := by
        apply GMap.ext; intro k
        show GMap.delete l h0 !! k = h0 !! k
        rw [GMap.lookup_delete_iff]; split <;> simp_all
      simp only [this, h0l]
      iintro ⟨Hσ, -⟩
      imodintro
      iframe Hσ

/-- The heap `h0` becomes `h'`, which differs from it only at the cells of `T`, all owned whole
(or absent): every cell of `T` that `h'` has is free (`Reading 0`), at a valid address. -/
theorem heap_reshape : ∀ (T : List Loc) (_hT : T.Nodup) (h0 h' : GMap Loc (NonAtomic val))
    (_hout : ∀ l, l ∉ T → h' !! l = h0 !! l)
    (_hmode : ∀ l ∈ T, ∀ x, h' !! l = some x → x.1 = Reading 0)
    (_haddr : ∀ l ∈ T, (h' !! l).isSome → 0 < l.addr ∧ l.addr < maxAddr),
    naHeapCtx tls h0 ∗ fullPts (GF := GF) h0 T ⊢ |==> (naHeapCtx tls h' ∗ fullPts h' T)
  | [], _, h0, h', hout, _, _ => by
    have : h' = h0 := GMap.ext fun k => hout k (by simp)
    subst this
    iintro ⟨Hσ, H⟩
    imodintro
    iframe
  | l :: T, hT, h0, h', hout, hmode, haddr => by
    have hlT : l ∉ T := (List.nodup_cons.1 hT).1
    let h1 := match h' !! l with | some x => <[l := x]> h0 | none => GMap.delete l h0
    have h1l : h1 !! l = h' !! l := by
      simp only [h1]; cases h'l : h' !! l <;> simp
    have h1k : ∀ k, k ≠ l → h1 !! k = h0 !! k := by
      intro k hk
      simp only [h1]; cases h' !! l
      · exact GMap.lookup_delete_ne _ (Ne.symm hk)
      · exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
    have hcongr : fullPts (GF := GF) h0 T = fullPts h1 T :=
      fullPts_congr fun k hk => (h1k k (fun e => hlT (e ▸ hk))).symm
    simp only [fullPts]
    iintro ⟨Hσ, Hl, HT⟩
    imod fullPt_step h0 h' l (hmode l List.mem_cons_self) (haddr l List.mem_cons_self)
      $$ [Hσ Hl] with ⟨Hσ, Hl⟩
    · iframe
    rw [hcongr]
    imod heap_reshape T (List.nodup_cons.1 hT).2 h1 h' (fun k hk => by
        by_cases e : k = l
        · subst e; exact h1l.symm
        · rw [h1k k e]; exact hout k (by simp [e, hk]))
      (fun k hk => hmode k (List.mem_cons_of_mem _ hk))
      (fun k hk => haddr k (List.mem_cons_of_mem _ hk)) $$ [Hσ HT] with ⟨Hσ, HT⟩
    · iframe
    imodintro
    iframe Hσ HT
    have : fullPt (GF := GF) h1 l = fullPt h' l := by simp only [fullPt, h1l]
    rw [← this]
    iexact Hl

end reshape

end Perennial
