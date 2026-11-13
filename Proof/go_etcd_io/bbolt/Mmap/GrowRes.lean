/-
`DB.grow` (U4e, `notes/bbolt-proof-plan.md`): the writer's resources around `File.Truncate`, the
cells of the mapping past the file's end out of `wCells` and back (`grow_cells_out`,
`grow_cells_in`), and its page-cache bytes after the file grew (`wBytes_grow`: the new zeros join
the `W` slots).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.GrowPure
public import GooseLang.Ext.Fs.Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

omit hos in
/-- Consecutive whole slots' cells join. -/
theorem cells_slots_join (b : Loc) :
    ∀ (k j : Nat), ([∗list] s ∈ List.range' j k, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) ⊢
      ∃ vf, cellsR (GF := GF) b (4096 * j) (4096 * k) vf
  | 0, j => by
    iintro -
    iexists (fun _ => #())
    unfold cellsR
    simp only [Nat.mul_zero, List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, j => by
    rw [List.range'_succ]
    refine BigSepL.bigSepL_cons.1.trans ?_
    iintro ⟨H1, H2⟩
    ihave H2 := cells_slots_join b k (j + 1) $$ H2
    rw [show 4096 * (k + 1) = 4096 + 4096 * k by omega]
    iapply cellsR_join b (4096 * j) 4096 (4096 * k)
    iframe H1
    rw [show 4096 * j + 4096 = 4096 * (j + 1) by omega]
    iexact H2

omit [GooseSemantics] hos in
/-- Consecutive whole slots' cells, split. -/
theorem cells_slots_split (b : Loc) :
    ∀ (k j : Nat), (∃ vf, cellsR (GF := GF) b (4096 * j) (4096 * k) vf) ⊢
      [∗list] s ∈ List.range' j k, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf
  | 0, j => by
    iintro -
    simp only [List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, j => by
    rw [List.range'_succ]
    refine Entails.trans ?_ BigSepL.bigSepL_cons.2
    iintro ⟨%vf, H⟩
    rw [show 4096 * (k + 1) = 4096 + 4096 * k by omega]
    icases (cellsR_append b (4096 * j) 4096 (4096 * k) vf).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists vf; iexact H1
    · iapply cells_slots_split b k (j + 1)
      iexists vf
      rw [show 4096 * (j + 1) = 4096 * j + 4096 by omega]
      iexact H2

omit [GooseSemantics] [GooseInterp] go_gctx hos in
/-- `wSlots n` is `wSlots j` and the slots `[j, n)`, when all of these are `W` slots. -/
theorem wSlots_split_perm (C : CommitSt) (fl : FLPg) (j n : Nat) (hjn : j ≤ n)
    (hs : ∀ s, j ≤ s → s < n → 2 ≤ s ∧ s ∉ slotsOf C fl) :
    (wSlots n C fl).Perm (wSlots j C fl ++ List.range' j (n - j)) := by
  refine (List.perm_ext_iff_of_nodup (wSlots_nodup _ _ _) ?_).2 fun s => ?_
  · refine List.nodup_append.2 ⟨wSlots_nodup _ _ _, List.nodup_range', ?_⟩
    intro a ha c hc hac
    subst hac
    have := ((mem_wSlots _ _ _ a).1 ha).2.1
    have := (List.mem_range'_1.1 hc).1
    omega
  · rw [List.mem_append, mem_wSlots, mem_wSlots, List.mem_range'_1]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases h : s < j
      · exact .inl ⟨h1, h, h3⟩
      · exact .inr ⟨by omega, by omega⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨(hs s h1 (by omega)).1, by omega, (hs s h1 (by omega)).2⟩

omit hos in
/-- **The cells of the mapping `(b, L)` from `lo` on, out of the writer's** (`wCells_gather'`'s
form): the slots below `j = lo / 4096` stay, the cells `[4096·j, lo)` stay, the cells `[lo, L)`
go (every slot from `j` on is a `W` slot). -/
theorem grow_cells_out (C : CommitSt) (fl : FLPg) (b : Loc) (L lo : Nat) (hlo : lo ≤ L)
    (hs : ∀ s, lo / 4096 ≤ s → s < L / 4096 → 2 ≤ s ∧ s ∉ slotsOf C fl) :
    ([∗list] s ∈ wSlots (L / 4096) C fl, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) ∗
      (∃ vf, cellsR (GF := GF) b (4096 * (L / 4096)) (L % 4096) vf) ⊢
    ([∗list] s ∈ wSlots (lo / 4096) C fl, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) ∗
      (∃ vf, cellsR (GF := GF) b (4096 * (lo / 4096)) (lo - 4096 * (lo / 4096)) vf) ∗
      (∃ vf, cellsR (GF := GF) b lo (L - lo) vf) := by
  have hj : lo / 4096 ≤ L / 4096 := Nat.div_le_div_right hlo
  iintro ⟨Hw, Hp⟩
  ihave Hw := (BigSepL.bigSepL_perm (Φ := fun s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s)
    4096 vf)) (wSlots_split_perm C fl (lo / 4096) (L / 4096) hj hs)).1 $$ Hw
  icases (BigSepL.bigSepL_append (Φ := fun _ s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s)
    4096 vf))).1 $$ Hw with ⟨Hlow, Hhi⟩
  iframe Hlow
  ihave Hhi := cells_slots_join b (L / 4096 - lo / 4096) (lo / 4096) $$ Hhi
  ihave Ht := cellsR_join b (4096 * (lo / 4096)) (4096 * (L / 4096 - lo / 4096)) (L % 4096)
    $$ [Hhi Hp]
  · iframe Hhi
    rw [show 4096 * (lo / 4096) + 4096 * (L / 4096 - lo / 4096) = 4096 * (L / 4096) by omega]
    iexact Hp
  icases Ht with ⟨%vf, Ht⟩
  rw [show 4096 * (L / 4096 - lo / 4096) + L % 4096 = L - 4096 * (lo / 4096) by omega]
  rw [show L - 4096 * (lo / 4096) = (lo - 4096 * (lo / 4096)) + (L - lo) by omega]
  icases (cellsR_append b (4096 * (lo / 4096)) (lo - 4096 * (lo / 4096)) (L - lo) vf).1 $$ Ht
    with ⟨H1, H2⟩
  isplitl [H1]
  · iexists vf; iexact H1
  · iexists vf
    rw [show 4096 * (lo / 4096) + (lo - 4096 * (lo / 4096)) = lo by omega]
    iexact H2

omit hos in
/-- **`grow_cells_out` reversed**, into `wCells` of `wSlots k` for any `k` at least the mapping's
slot count (`wCells_carve`). -/
theorem grow_cells_in (C : CommitSt) (fl : FLPg) (b : Loc) (L lo k : Nat) (hlo : lo ≤ L)
    (hk : L / 4096 ≤ k)
    (hs : ∀ s, lo / 4096 ≤ s → s < L / 4096 → 2 ≤ s ∧ s ∉ slotsOf C fl) :
    ([∗list] s ∈ wSlots (lo / 4096) C fl, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) ∗
      (∃ vf, cellsR (GF := GF) b (4096 * (lo / 4096)) (lo - 4096 * (lo / 4096)) vf) ∗
      (∃ vf, cellsR (GF := GF) b lo (L - lo) vf) ⊢
    wCells (GF := GF) (some (b, L)) (wSlots k C fl) := by
  have hj : lo / 4096 ≤ L / 4096 := Nat.div_le_div_right hlo
  refine Entails.trans ?_ (wCells_carve C fl b L k hk)
  iintro ⟨Hlow, H1, H2⟩
  ihave Ht := cellsR_join b (4096 * (lo / 4096)) (lo - 4096 * (lo / 4096)) (L - lo) $$ [H1 H2]
  · iframe H1
    rw [show 4096 * (lo / 4096) + (lo - 4096 * (lo / 4096)) = lo by omega]
    iexact H2
  icases Ht with ⟨%vf, Ht⟩
  rw [show lo - 4096 * (lo / 4096) + (L - lo) =
    4096 * (L / 4096 - lo / 4096) + L % 4096 by omega]
  icases (cellsR_append b (4096 * (lo / 4096)) (4096 * (L / 4096 - lo / 4096)) (L % 4096) vf).1
    $$ Ht with ⟨Hhi, Hp⟩
  isplitr [Hp]
  · iapply (BigSepL.bigSepL_perm (Φ := fun s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s)
      4096 vf)) (wSlots_split_perm C fl (lo / 4096) (L / 4096) hj hs)).2
    iapply (BigSepL.bigSepL_append (Φ := fun _ s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s)
      4096 vf))).2
    iframe Hlow
    iapply cells_slots_split b (L / 4096 - lo / 4096) (lo / 4096)
    iexists vf; iexact Hhi
  · iexists vf
    rw [show 4096 * (lo / 4096) + 4096 * (L / 4096 - lo / 4096) = 4096 * (L / 4096) by omega]
    iexact Hp

omit go_gctx in
/-- A file's page-cache bytes, cut in two. -/
theorem growBytes_app (p : BFile) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    osBytes (GF := GF) p.ino off dq (xs ++ ys) ⊣⊢
      osBytes (GF := GF) p.ino off dq xs ∗ osBytes (GF := GF) p.ino (off + xs.length) dq ys := by
  unfold osBytes; exact bytesG_append _ _ _ _ _ _

omit go_gctx in
theorem growBytes_nil (p : BFile) (off : Nat) (dq : DFrac) :
    ⊢ osBytes (GF := GF) p.ino off dq [] := by
  unfold osBytes; exact (bytesG_nil _ _ _ _).2

/-- Bytes of the file `p` from `off` whose values are `n` zeros (their crash candidates any). -/
def zBytes (p : BFile) (off n : Nat) : IProp GF :=
  iprop(∃ xs : List ByteG, osBytes p.ino off (DFrac.own 1) xs ∗
    ⌜xs.map Prod.fst = List.replicate n (0 : w8)⌝)

omit go_gctx in
/-- Zero bytes, cut in two. -/
theorem zBytes_app (p : BFile) (off a b : Nat) :
    zBytes (GF := GF) p off (a + b) ⊢ zBytes (GF := GF) p off a ∗ zBytes (GF := GF) p (off + a) b := by
  unfold zBytes
  iintro ⟨%xs, H, %hx⟩
  have hl : xs.length = a + b := by simpa using congrArg List.length hx
  have hs := growBytes_app (GF := GF) p off (DFrac.own 1) (xs.take a) (xs.drop a)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left (by omega)] at hs
  icases hs.1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists xs.take a; iframe H1; ipureintro
    rw [List.map_take, hx, List.take_replicate, Nat.min_eq_left (by omega)]
  · iexists xs.drop a; iframe H2; ipureintro
    rw [List.map_drop, hx, List.drop_replicate, Nat.add_sub_cancel_left]

/-- The new zeros of slot `s` after the file grew from `size`: from `size` or the slot's start, to
its end. -/
def zSlot (p : BFile) (size s : Nat) : IProp GF :=
  zBytes p (max size (4096 * s)) (4096 * (s + 1) - max size (4096 * s))

omit go_gctx in
/-- New zeros from `size` (or slot `j`'s start) to the end of slot `j + k - 1`, by slot. -/
theorem zeros_split (p : BFile) (size : Nat) :
    ∀ (k j : Nat), size / 4096 ≤ j →
      zBytes (GF := GF) p (max size (4096 * j)) (4096 * (j + k) - max size (4096 * j)) ⊢
      [∗list] s ∈ List.range' j k, zSlot (GF := GF) p size s
  | 0, j, _ => by
    iintro -
    simp only [List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, j, hj => by
    have hM : max size (4096 * (j + 1)) = 4096 * (j + 1) := by omega
    rw [show 4096 * (j + (k + 1)) - max size (4096 * j) =
      (4096 * (j + 1) - max size (4096 * j)) +
        (4096 * ((j + 1) + k) - max size (4096 * (j + 1))) by omega, List.range'_succ]
    refine (zBytes_app p _ _ _).trans ?_
    refine Entails.trans ?_ BigSepL.bigSepL_cons.2
    refine sep_mono .rfl ?_
    rw [show max size (4096 * j) + (4096 * (j + 1) - max size (4096 * j)) =
        max size (4096 * (j + 1)) by omega]
    exact zeros_split p size k (j + 1) (by omega)

/-- **The writer's page-cache bytes after the file grew from `size` to `S`** (whole pages): the
new zeros join the `W` slots reaching past the old end (`growWb`), given that the partial last
page's bytes are the file's whole. -/
theorem wBytes_grow (p : BFile) (W : List Nat) (wb : Nat → List w8) (size S : Nat)
    (hn : W.Nodup) (hS : S % 4096 = 0) (hle : size ≤ S)
    (hp : ∀ s ∈ W, 4096 * s < size → size < 4096 * (s + 1) → size - 4096 * s ≤ (wb s).length) :
    wBytes (GF := GF) p W wb size ∗
      zBytes (GF := GF) p size (S - size) ⊢
    wBytes (GF := GF) p W (growWb wb size) S := by
  have hz := zeros_split (GF := GF) p size (S / 4096 - size / 4096) (size / 4096) (Nat.le_refl _)
  rw [show max size (4096 * (size / 4096)) = size by omega,
    show 4096 * (size / 4096 + (S / 4096 - size / 4096)) = S by omega] at hz
  let q : Nat → Bool := fun s => decide (size < 4096 * (s + 1) ∧ 4096 * (s + 1) ≤ S)
  have hsub : ([∗list] s ∈ List.range' (size / 4096) (S / 4096 - size / 4096),
      zSlot (GF := GF) p size s) ⊢ [∗list] s ∈ W.filter q, zSlot (GF := GF) p size s := by
    refine bigSepL_sub_nodup _ _ (List.Pairwise.filter _ hn) fun s hs => ?_
    rw [List.mem_filter] at hs
    simp only [q, decide_eq_true_eq] at hs
    rw [List.mem_range'_1]
    omega
  have hite := (bigSepL_ite_filter (GF := GF) q (fun s => zSlot (GF := GF) p size s) W).2
  refine (sep_mono .rfl (hz.trans (hsub.trans hite))).trans ?_
  unfold wBytes
  refine (BigSepL.bigSepL_sep_eqv_symm (Φ := fun _ s => iprop(if 4096 * (s + 1) ≤ size then
      iprop(∃ xs : List ByteG, osBytes (GF := GF) p.ino (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = wb s⌝)
    else if 4096 * s < size then
      iprop(∃ xs : List ByteG, osBytes (GF := GF) p.ino (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = (wb s).take (size - 4096 * s)⌝)
    else iprop(emp)))
    (Ψ := fun _ s => iprop(if q s then zSlot (GF := GF) p size s else iprop(emp)))).1.trans ?_
  refine bigSepL_mono_mem' fun s hs => ?_
  by_cases h1 : 4096 * (s + 1) ≤ size
  · have hq : q s = false := by simp only [q]; simp; omega
    simp only [h1, hq, growWb, ↓reduceIte, Bool.false_eq_true,
      show 4096 * (s + 1) ≤ S by omega]
    iintro ⟨H, -⟩; iexact H
  by_cases h2 : 4096 * (s + 1) ≤ S
  · have hq : q s = true := by simp only [q]; simp; omega
    simp only [h1, h2, hq, ↓reduceIte]
    by_cases h3 : 4096 * s < size
    · simp only [h3, ↓reduceIte, zSlot, zBytes, show max size (4096 * s) = size by omega]
      iintro ⟨⟨%xs, Hx, %hx⟩, %zs, Hz, %hz⟩
      have hlen : xs.length = size - 4096 * s := by
        have := congrArg List.length hx
        rw [List.length_map, List.length_take] at this
        have := hp s hs h3 (by omega)
        omega
      iexists xs ++ zs
      isplitl
      · iapply (growBytes_app p _ _ _ _).2
        iframe Hx
        rw [hlen, show 4096 * s + (size - 4096 * s) = size by omega]
        iexact Hz
      · ipureintro
        simp only [growWb, h1, ↓reduceIte, List.map_append, hx, hz]
        congr 2
        omega
    · simp only [h3, ↓reduceIte, zSlot, zBytes, show max size (4096 * s) = 4096 * s by omega]
      iintro ⟨-, %zs, Hz, %hz⟩
      iexists zs
      iframe Hz
      ipureintro
      simp only [growWb, h1, ↓reduceIte, hz,
        show size - 4096 * s = 0 by omega, List.take_zero, List.nil_append]
      congr 1
      omega
  · have hq : q s = false := by simp only [q]; simp; omega
    simp only [h1, h2, hq, ↓reduceIte, Bool.false_eq_true,
      show ¬ 4096 * s < size by omega, show ¬ 4096 * s < S by omega]
    iintro -
    iempintro

end res

end bbolt
end EtcdGrove
end Perennial
