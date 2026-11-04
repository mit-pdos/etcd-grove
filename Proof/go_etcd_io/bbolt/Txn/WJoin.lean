/-
Slots leaving the store join the writer's `W` slots (U5 of `notes/bbolt-proof-plan.md`; for
`beginRWTx`'s `ReleasePendingPages` and the writer's `Rollback`): `slotsOwn`'s cell halves become
`wCells`' whole-slot cells, its page-cache bytes `wBytes`' (each slot whole inside the mapping
and the file).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Cells

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section wjoin
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The `W` slots' bytes `wb` with the slots `S`' bytes `bs` in place. -/
def mergeWb (S : List Nat) (bs wb : Nat → List w8) : Nat → List w8 :=
  fun s => if s ∈ S then bs s else wb s

/-- **Slots `S` join the `W` slots**: `S` disjoint from `W`, each slot of `S` whole inside the
file and the mapping, its bytes a page. -/
theorem wjoin (p : GoString) (ms : MapSt) (W S : List Nat) (wb bs : Nat → List w8) (size : Nat)
    (hdisj : ∀ s ∈ S, s ∉ W)
    (hS : ∀ s ∈ S, 4096 * (s + 1) ≤ size ∧ (∀ b l, ms = some (b, l) → 4096 * (s + 1) ≤ l) ∧
      (bs s).length = 4096) :
    wCells (GF := GF) ms W ∗ wBytes p W wb size ∗ slotsOwn ms p S bs ⊢
      wCells ms (W ++ S) ∗ wBytes p (W ++ S) (mergeWb S bs wb) size := by
  -- the `W` slots' bytes are unchanged
  have hW : wBytes (GF := GF) p W wb size ⊢ wBytes p W (mergeWb S bs wb) size := by
    unfold wBytes
    refine BigSepL.bigSepL_mono fun {k x} hk => ?_
    have hx : x ∉ S := fun h => hdisj x h (List.mem_of_getElem? hk)
    simp only [mergeWb, hx, ↓reduceIte]
    exact .rfl
  -- the bytes of `S`
  have hSb : ([∗list] s ∈ S, osSlot (GF := GF) p s (bs s)) ⊢
      [∗list] s ∈ S, (if 4096 * (s + 1) ≤ size then
        iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗
          ⌜xs.map Prod.fst = mergeWb S bs wb s⌝)
        else if 4096 * s < size then
          iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗
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

/-- The bytes of the extent from `f` read from `wb'`, which agrees with `wb` wherever an id of
`fl` is not, are `wb`'s, when `flCurOK` holds of them and `f`'s bytes hold a page header. -/
omit [GooseSemantics] [GooseInterp] go_gctx hos in
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

end wjoin

end bbolt
end EtcdGrove
end Perennial
