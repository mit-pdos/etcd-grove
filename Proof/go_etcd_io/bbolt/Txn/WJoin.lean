/-
Slots leaving the store join the writer's `W` slots (U5 of `notes/bbolt-proof-plan.md`; for
`beginRWTx`'s `ReleasePendingPages` and the writer's `Rollback`): `slotsOwn`'s cell halves become
`wCells`' whole-slot cells, its page-cache bytes `wBytes`' (each slot whole inside the mapping
and the file).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Cells
public import Proof.go_etcd_io.bbolt.Txn.FLFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section wjoin
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The `W` slots' bytes `wb` with the slots `S`' bytes `bs` in place. -/
def mergeWb (S : List Nat) (bs wb : Nat → List w8) : Nat → List w8 :=
  fun s => if s ∈ S then bs s else wb s

/-- **Slots `S` join the `W` slots**, the cells' and the bytes' lists apart (session S4: the
writer's bytes are over `W` but the synced freelist page's slots, `wBytesX`). -/
theorem wjoin2 (p : BFile) (ms : MapSt) (Wc Wb S : List Nat) (wb bs : Nat → List w8) (size : Nat)
    (hdisj : ∀ s ∈ S, s ∉ Wb)
    (hS : ∀ s ∈ S, 4096 * (s + 1) ≤ size ∧ (∀ b l, ms = some (b, l) → 4096 * (s + 1) ≤ l) ∧
      (bs s).length = 4096) :
    wCells (GF := GF) ms Wc ∗ wBytes p Wb wb size ∗ slotsOwn ms p S bs ⊢
      wCells ms (Wc ++ S) ∗ wBytes p (Wb ++ S) (mergeWb S bs wb) size := by
  -- the `W` slots' bytes are unchanged
  have hW : wBytes (GF := GF) p Wb wb size ⊢ wBytes p Wb (mergeWb S bs wb) size := by
    unfold wBytes
    refine BigSepL.bigSepL_mono fun {k x} hk => ?_
    have hx : x ∉ S := fun h => hdisj x h (List.mem_of_getElem? hk)
    simp only [mergeWb, hx, ↓reduceIte]
    exact .rfl
  -- the bytes of `S`
  have hSb : ([∗list] s ∈ S, osSlot (GF := GF) p s (bs s)) ⊢
      [∗list] s ∈ S, (if 4096 * (s + 1) ≤ size then
        iprop(∃ xs : List ByteG, bBytes p (4096 * s) (DFrac.own 1) xs ∗
          ⌜xs.map Prod.fst = mergeWb S bs wb s⌝)
        else if 4096 * s < size then
          iprop(∃ xs : List ByteG, bBytes p (4096 * s) (DFrac.own 1) xs ∗
            ⌜xs.map Prod.fst = (mergeWb S bs wb s).take (size - 4096 * s)⌝)
        else iprop(emp)) := by
    refine BigSepL.bigSepL_mono fun {k x} hk => ?_
    have hx := List.mem_of_getElem? hk
    simp only [mergeWb, hx, ↓reduceIte, (hS x hx).1]
    exact .rfl
  rcases ms with _ | ⟨base, len⟩
  · unfold wCells slotsOwn
    simp only
    iintro ⟨-, Hb, Hs⟩
    ihave Hb := hW $$ Hb
    unfold wBytes
    isplitr
    · iempintro
    iapply BigSepL.bigSepL_append.2
    iframe Hb
    iapply hSb
    iapply BigSepL.bigSepL_mono (Φ := fun _ s => iprop(emp ∗ osSlot (GF := GF) p s (bs s))) $$ Hs
    intro k x _
    iintro ⟨-, H⟩; iexact H
  · unfold wCells slotsOwn
    simp only
    iintro ⟨⟨Hc, Hpart⟩, Hb, Hs⟩
    ihave Hb := hW $$ Hb
    ihave ⟨Hsc, Hsb⟩ := (BigSepL.bigSepL_sep_eqv (Φ := fun _ s =>
      bytesPointsto (GF := GF) (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s))
      (Ψ := fun _ s => osSlot (GF := GF) p s (bs s)) (l := S)).1 $$ Hs
    unfold wBytes
    isplitl [Hc Hpart Hsc]
    rotate_left
    · iapply BigSepL.bigSepL_append.2
      iframe Hb
      iapply hSb; iexact Hsb
    iframe Hpart
    iapply BigSepL.bigSepL_append.2
    iframe Hc
    iapply BigSepL.bigSepL_mono (Φ := fun _ s =>
      bytesPointsto (GF := GF) (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s))
      $$ Hsc
    intro k x hk
    have hx := List.mem_of_getElem? hk
    obtain ⟨-, hl, hlen⟩ := hS x hx
    simp only [hl base len rfl, ↓reduceIte]
    iintro H
    ihave H := bytes_cellsR base (bs x) (4096 * x) $$ H
    rw [hlen]
    iexists _; iexact H



/-- **Slots `S` join the `W` slots**: `S` disjoint from `W`, each slot of `S` whole inside the
file and the mapping, its bytes a page. -/
theorem wjoin (p : BFile) (ms : MapSt) (W S : List Nat) (wb bs : Nat → List w8) (size : Nat)
    (hdisj : ∀ s ∈ S, s ∉ W)
    (hS : ∀ s ∈ S, 4096 * (s + 1) ≤ size ∧ (∀ b l, ms = some (b, l) → 4096 * (s + 1) ≤ l) ∧
      (bs s).length = 4096) :
    wCells (GF := GF) ms W ∗ wBytes p W wb size ∗ slotsOwn ms p S bs ⊢
      wCells ms (W ++ S) ∗ wBytes p (W ++ S) (mergeWb S bs wb) size :=
  wjoin2 p ms W W S wb bs size hdisj hS

/-- **The synced freelist page's slots `X` join the `W` slots' cells** (session S4): their cells
join `wCells`, their half bytes stay apart (`wBytesX`'s second part). -/
theorem wjoinH (p : BFile) (ms : MapSt) (Wc X : List Nat) (bs : Nat → List w8)
    (hX : ∀ s ∈ X, (∀ b l, ms = some (b, l) → 4096 * (s + 1) ≤ l) ∧ (bs s).length = 4096) :
    wCells (GF := GF) ms Wc ∗ slotsOwnH ms p X bs ⊢
      wCells ms (Wc ++ X) ∗ [∗list] s ∈ X, osSlotH p s (bs s) := by
  rcases ms with _ | ⟨base, len⟩
  · unfold wCells slotsOwnH
    simp only
    iintro ⟨-, Hs⟩
    isplitr
    · iempintro
    iapply BigSepL.bigSepL_mono (Φ := fun _ s => iprop(emp ∗ osSlotH (GF := GF) p s (bs s))) $$ Hs
    intro k x _
    iintro ⟨-, H⟩; iexact H
  · unfold wCells slotsOwnH
    simp only
    iintro ⟨⟨Hc, Hpart⟩, Hs⟩
    ihave ⟨Hsc, Hsb⟩ := (BigSepL.bigSepL_sep_eqv (Φ := fun _ s =>
      bytesPointsto (GF := GF) (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s))
      (Ψ := fun _ s => osSlotH (GF := GF) p s (bs s)) (l := X)).1 $$ Hs
    iframe Hsb Hpart
    iapply BigSepL.bigSepL_append.2
    iframe Hc
    iapply BigSepL.bigSepL_mono (Φ := fun _ s =>
      bytesPointsto (GF := GF) (base +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (bs s))
      $$ Hsc
    intro k x hk
    have hx := List.mem_of_getElem? hk
    obtain ⟨hl, hlen⟩ := hX x hx
    simp only [hl base len rfl, ↓reduceIte]
    iintro H
    ihave H := bytes_cellsR base (bs x) (4096 * x) $$ H
    rw [hlen]
    iexists _; iexact H

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- The bytes of the extent from `f` read from `wb'`, which agrees with `wb` wherever an id of
`fl` is not, are `wb`'s, when `flCurOK` holds of them and `f`'s bytes hold a page header. -/
theorem extentBytes_congr (fl : FLPg) (C : CommitSt) (wb wb' : Nat → List w8) (f : Nat)
    (hf : C.flpg = some f) (h : flCurOK fl C (extentBytes wb f)) (h16 : 16 ≤ (wb f).length)
    (hhwm : C.hwm < 2 ^ 64)
    (hag : ∀ s : Nat, s < 2 ^ 64 → W64 (s : Int) ∉ fl.allIds → wb' s = wb s) :
    extentBytes wb' f = extentBytes wb f := by
  have ha9 := (h f hf).2.2.2.2.2.2.2.2.1
  have hlt : f + (1 + pageOverflow (extentBytes wb f)) ≤ C.hwm := (h f hf).2.1
  have hov : pageOverflow (extentBytes wb f) = pageOverflow (wb f) := by
    unfold pageOverflow pageHdr bytesAt
    congr 3
    unfold extentBytes
    rw [show 1 + pageOverflow (wb f) = (pageOverflow (wb f)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, List.drop_zero, List.drop_zero,
      List.take_append_of_le_length h16]
  rw [hov] at ha9 hlt
  have hf' : wb' f = wb f := hag f (by omega) (ha9 f (Nat.le_refl _) (by omega)).2
  unfold extentBytes
  rw [hf']
  simp only [List.flatMap]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  rw [List.mem_range'] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact hag _ (by omega) (ha9 _ (by omega) (by omega)).2

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- **The synced freelist page's bytes hold a header** (`wdb_release`'s and `wdb_rollback`'s, from
`wdbOK`'s batch-37 clause: a `W` slot inside the file holds a page's bytes): the page is a `W`
slot (`flCurOK`: no tree slot, no free or pending id, below the high-water mark). -/
theorem wb_header (w : WDb) (hok : wdbOK w) :
    ∀ f, w.C.flpg = some f → 16 ≤ (w.wb f).length := by
  intro f hf
  have hlen := hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, c3, c4, -, c6, -⟩ := hok
  obtain ⟨h2, hlt, -, -, -, -, -, -, h9, -⟩ := c6 f hf f hf
  obtain ⟨hcov, hall⟩ := h9 f (Nat.le_refl _) (by omega)
  have hW : f ∈ w.W := by
    refine (c4 f).2 ⟨h2, ?_, fun ht => hcov ((mem_pagesSlots_iff _ _).1 ht), fun hp => ?_⟩
    · have := Nat.le_max_right (mapLen w.ms) w.m.size; omega
    · obtain ⟨t, pd, x, hpd, hx, hxs⟩ := (pendSlots_mem_iff _ _).1 hp
      apply hall
      have : W64 (f : Int) = x := by rw [← hxs, W64_toNat_self]
      rw [this]
      exact List.mem_append_right _ ((pendingIds_mem_iff _ _).2 ⟨t, pd, hpd, hx⟩)
  rw [hlen f hW (by omega)]; omega

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- **The synced freelist page's half is no pending slot under `wdbOK`** (session S4): `flCurOK`
keeps the page's slots out of the freelist. -/
theorem flxS_not_pend (w : WDb) (hok : wdbOK w) :
    ∀ s ∈ flxS w.C w.fl w.wb, s ∉ pendSlots w.fl := by
  intro s hs hp
  unfold flxS at hs
  rcases hf : w.C.flpg with _ | f
  · rw [hf] at hs; cases hs
  · rw [hf] at hs
    by_cases hfp : f ∈ pendSlots w.fl
    · simp only [hfp, ↓reduceIte] at hs; cases hs
    · simp only [hfp, ↓reduceIte] at hs
      have h16 := wb_header w hok f hf
      obtain ⟨-, -, -, -, -, -, -, -, hsl, -⟩ := hok.2.2.2.2.2.1 f hf f hf
      rw [mem_flExt] at hs
      rw [pageOverflow_extentBytes _ _ h16] at hsl
      exact (hsl s hs.1 hs.2).2 (mem_allIds_of_pend _ _ hp).1

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- The synced freelist page is not pending under `wdbOK` (`flCurOK`). -/
theorem flpg_not_pend (w : WDb) (hok : wdbOK w) :
    ∀ f, w.C.flpg = some f → f ∉ pendSlots w.fl := by
  intro f hf hp
  obtain ⟨-, -, -, -, -, -, -, -, hsl, -⟩ := hok.2.2.2.2.2.1 f hf f hf
  exact (hsl f (Nat.le_refl _) (by omega)).2 (mem_allIds_of_pend _ _ hp).1

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- `flxS` reads the page's pendingness and its header's bytes only. -/
theorem flxS_congr_f (C : CommitSt) (fl fl' : FLPg) (b b' : Nat → List w8)
    (h : ∀ f, C.flpg = some f → (f ∈ pendSlots fl' ↔ f ∈ pendSlots fl) ∧ b' f = b f) :
    flxS C fl' b' = flxS C fl b := by
  unfold flxS
  rcases hf : C.flpg with _ | f
  · rfl
  · obtain ⟨h1, h2⟩ := h f hf
    simp only [h1]
    unfold flExt
    rw [h2]

/-- `wBytes` reads its slots' bytes only. -/
theorem wBytes_congr (p : BFile) (W : List Nat) (wb wb' : Nat → List w8) (size : Nat)
    (h : ∀ s ∈ W, wb' s = wb s) :
    wBytes (GF := GF) p W wb size ⊢ wBytes p W wb' size := by
  unfold wBytes
  refine BigSepL.bigSepL_mono fun {k x} hk => ?_
  rw [h x (List.mem_of_getElem? hk)]

/-- `osSlotH`s read their slots' bytes only. -/
theorem osSlotsH_congr (p : BFile) (X : List Nat) (wb wb' : Nat → List w8)
    (h : ∀ s ∈ X, wb' s = wb s) :
    ([∗list] s ∈ X, osSlotH (GF := GF) p s (wb s)) ⊢ [∗list] s ∈ X, osSlotH p s (wb' s) := by
  refine BigSepL.bigSepL_mono fun {k x} hk => ?_
  rw [h x (List.mem_of_getElem? hk)]

/-- **Slots `S` join the `W` slots, the writer holding the synced freelist page's half `X`**
(session S4: `wjoin` over `wBytesX`; `S` meets neither `W` nor `X`). -/
theorem wjoinX (p : BFile) (ms : MapSt) (W X S : List Nat) (wb bs : Nat → List w8) (size : Nat)
    (hdisj : ∀ s ∈ S, s ∉ W) (hX : ∀ s ∈ S, s ∉ X)
    (hS : ∀ s ∈ S, 4096 * (s + 1) ≤ size ∧ (∀ b l, ms = some (b, l) → 4096 * (s + 1) ≤ l) ∧
      (bs s).length = 4096) :
    wCells (GF := GF) ms W ∗ wBytesX p W X wb size ∗ slotsOwn ms p S bs ⊢
      wCells ms (W ++ S) ∗ wBytesX p (W ++ S) X (mergeWb S bs wb) size := by
  have hj := wjoin2 (GF := GF) p ms W (W.filter (fun s => decide (s ∉ X))) S wb bs size
    (fun s hs hw => hdisj s hs (List.mem_filter.1 hw).1) hS
  have hfilt : (W ++ S).filter (fun s => decide (s ∉ X)) = W.filter (fun s => decide (s ∉ X)) ++ S := by
    rw [List.filter_append]
    congr 1
    rw [List.filter_eq_self]; intro s hs; simp [hX s hs]
  iintro ⟨Hc, Hbx, HS⟩
  iunfold wBytesX at Hbx
  icases Hbx with ⟨Hb, H0⟩
  ihave ⟨Hc, Hb⟩ := hj $$ [Hc Hb HS]
  · iframe
  iframe Hc
  unfold wBytesX
  rw [hfilt]
  iframe Hb
  iapply osSlotsH_congr p X wb (mergeWb S bs wb) ?_ $$ H0
  intro s hs
  have : s ∉ S := fun h => hX s h hs
  simp [mergeWb, this]

end wjoin

end bbolt
end EtcdGrove
end Perennial
