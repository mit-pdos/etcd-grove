/-
`Open`'s carving (U11d; design §3.11 "Open", between steps 1.4 and 2): the file's page-cache bytes
(`fileHolds`' `osBytes p.ino 0 1 xs`) and the new mapping's client halves (`DB.mmapUnlocked.spec_own`'s
post: the file's extent as bytes at a half, the rest any cells) cut by slot into
`Open/Core.open_core`'s inputs: the metas' page-cache halves and cell quarters, the store slots'
page-cache bytes and cells, the writer's `W` slots' page-cache bytes and cells (`W` the slots of
the mapping that are neither metas nor store slots), each slot's bytes `bytesAt ys (4096·s) 4096`.
What lies past the last whole slot of the mapping is dropped.
-/
module

public import Proof.go_etcd_io.bbolt.Open.CoreFacts
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.go_etcd_io.bbolt.Mmap.RemapGather
public import Proof.os.CrashFile

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section runs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The slot `s` of a run `ys` starting at offset 0. -/
def runSlot {α : Type} (ys : List α) (s : Nat) : List α := (ys.drop (4096 * s)).take 4096

theorem drop_runSlot {α : Type} (ys : List α) (i : Nat) :
    ys.drop (4096 * i) = runSlot ys i ++ ys.drop (4096 * (i + 1)) := by
  unfold runSlot
  conv => lhs; rw [← List.take_append_drop 4096 (ys.drop (4096 * i))]
  rw [List.drop_drop]
  congr 2

/-- **A run of something that splits at any point, by slot** (from slot `i`, `k` slots; slots
past the run's end are empty). -/
theorem runs_slots {α : Type} (Ψ : Nat → List α → IProp GF)
    (happ : ∀ o a b, Ψ o (a ++ b) ⊢ Ψ o a ∗ Ψ (o + a.length) b)
    (hnil : ∀ o o', Ψ o [] ⊢ Ψ o' []) (ys : List α) :
    ∀ k i, Ψ (4096 * i) (ys.drop (4096 * i)) ⊢
      [∗list] s ∈ List.range' i k, Ψ (4096 * s) (runSlot ys s)
  | 0, i => by
    iintro -
    simp only [List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, i => by
    rw [List.range'_succ]
    refine Entails.trans ?_ BigSepL.bigSepL_cons.2
    rw [drop_runSlot ys i]
    refine (happ _ _ _).trans (sep_mono .rfl ?_)
    refine Entails.trans ?_ (runs_slots Ψ happ hnil ys k (i + 1))
    by_cases h : (runSlot ys i).length = 4096
    · rw [h, show 4096 * i + 4096 = 4096 * (i + 1) by omega]
    · have hl : (runSlot ys i).length < 4096 := by
        have : (runSlot ys i).length ≤ 4096 := by
          unfold runSlot; simp only [List.length_take]; exact Nat.min_le_left _ _
        omega
      have he : ys.drop (4096 * (i + 1)) = [] := by
        unfold runSlot at hl
        simp only [List.length_take, List.length_drop] at hl
        apply List.drop_eq_nil_of_le; omega
      rw [he]; exact hnil _ _

end runs

section carve
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The file's page-cache bytes, by slot. -/
theorem osBytes_slots (p : BFile) (xs : List ByteG) :
    osBytes (GF := GF) p.ino 0 (DFrac.own 1) xs ⊢
      [∗list] s ∈ List.range xs.length, osBytes (GF := GF) p.ino (4096 * s) (DFrac.own 1)
        (runSlot xs s) := by
  have h := runs_slots (GF := GF) (fun o ys => osBytes (GF := GF) p.ino o (DFrac.own 1) ys)
    (fun o a b => by unfold osBytes; exact (bytesG_append _ _ _ _ _ _).1)
    (fun o o' => (osBytes_nil' p o _).1.trans (osBytes_nil' p o' _).2) xs xs.length 0
  simp only [Nat.mul_zero, List.drop_zero] at h
  rw [List.range_eq_range']
  exact h

theorem runSlot_map {α β : Type} (f : α → β) (ys : List α) (s : Nat) :
    (runSlot ys s).map f = runSlot (ys.map f) s := by
  unfold runSlot; rw [List.map_take, List.map_drop]

theorem runSlot_map_fst (xs : List ByteG) (s : Nat) :
    (runSlot xs s).map Prod.fst = bytesAt (xs.map Prod.fst) (4096 * s) 4096 := by
  rw [runSlot_map]; rfl

/-- The values of the opened mapping's cells: the file's bytes, then `vf`. -/
def openVf (ys : List w8) (vf : Nat → val) : Nat → val :=
  fun i => if i < ys.length then bytesVf 0 ys i else vf i

theorem openVf_slot (ys : List w8) (vf : Nat → val) (s : Nat) (hs : 4096 * (s + 1) ≤ ys.length)
    (i : Nat) (h1 : 4096 * s ≤ i) (h2 : i < 4096 * s + 4096) :
    openVf ys vf i = bytesVf (4096 * s) (bytesAt ys (4096 * s) 4096) i := by
  unfold openVf bytesVf bytesAt
  simp only [show i < ys.length from by omega, ↓reduceIte]
  congr 2
  simp only [Nat.sub_zero, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    show i - 4096 * s < 4096 from by omega, ↓reduceIte]
  congr 2
  omega

/-- The opened mapping's cells, whole: the file's bytes at a half and the rest. -/
theorem open_cells (b : Loc) (ys : List w8) (L : Nat) (vf : Nat → val) (hL : ys.length ≤ L) :
    bytesPointsto (GF := GF) b (DFrac.own (1 : Qp).half) ys ∗
      cellsR (GF := GF) b ys.length (L - ys.length) vf ⊢
      cellsR (GF := GF) b 0 L (openVf ys vf) := by
  have h := bytes_cellsR (GF := GF) b ys 0
  rw [Int.natCast_zero, loc_add_0] at h
  have hj := (cellsR_append (GF := GF) b 0 ys.length (L - ys.length) (openVf ys vf)).2
  rw [show ys.length + (L - ys.length) = L by omega, Nat.zero_add] at hj
  refine Entails.trans (sep_mono h .rfl) (Entails.trans ?_ hj)
  refine sep_mono (cellsR_congr _ _ _ _ _ fun i _ h2 => ?_).1
    (cellsR_congr _ _ _ _ _ fun i h1 _ => ?_).1
  · unfold openVf; simp only [show i < ys.length from by omega, ↓reduceIte]
  · unfold openVf; simp only [show ¬ i < ys.length from by omega, ↓reduceIte]

/-- A whole slot inside the file: its cells are its bytes at a half. -/
theorem open_slot_bytes (b : Loc) (ys : List w8) (vf : Nat → val) (s : Nat)
    (hs : 4096 * (s + 1) ≤ ys.length) :
    cellsR (GF := GF) b (4096 * s) 4096 (openVf ys vf) ⊢
      bytesPointsto (GF := GF) (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half)
        (bytesAt ys (4096 * s) 4096) := by
  have hl : (bytesAt ys (4096 * s) 4096).length = 4096 := by
    unfold bytesAt; simp; omega
  have h := cellsR_bytes (GF := GF) b (bytesAt ys (4096 * s) 4096) (4096 * s)
  rw [hl] at h
  exact (cellsR_congr _ _ _ _ _ (openVf_slot ys vf s hs)).1.trans h

theorem runSlot_length_full {α : Type} (ys : List α) (s : Nat) (h : 4096 * (s + 1) ≤ ys.length) :
    (runSlot ys s).length = 4096 := by
  unfold runSlot; simp only [List.length_take, List.length_drop]; omega

/-- The metas' page-cache bytes, from slots 0 and 1. -/
theorem open_metaOs (p : BFile) (C : CommitSt) (xs : List ByteG)
    (himg : fileImage (xs.map Prod.fst) C) (h8 : 8192 ≤ xs.length) :
    osBytes (GF := GF) p.ino (4096 * 0) (DFrac.own 1) (runSlot xs 0) ∗
      osBytes (GF := GF) p.ino (4096 * 1) (DFrac.own 1) (runSlot xs 1) ⊢
    metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ∗
      metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C := by
  have h0 := runSlot_length_full xs 0 (by omega)
  have e : 4096 * 1 = 0 + (runSlot xs 0).length := by rw [h0]
  rw [e, Nat.mul_zero]
  have hj : osBytes (GF := GF) p.ino 0 (DFrac.own 1) (runSlot xs 0) ∗
      osBytes (GF := GF) p.ino (0 + (runSlot xs 0).length) (DFrac.own 1) (runSlot xs 1) ⊢
      osBytes (GF := GF) p.ino 0 (DFrac.own 1) (runSlot xs 0 ++ runSlot xs 1) := by
    unfold osBytes; exact (bytesG_append _ _ _ _ _ _).2
  refine hj.trans ((osBytes_halves p 0 _).1.trans ?_)
  have hm : (runSlot xs 0 ++ runSlot xs 1).map Prod.fst = C.m0 ++ C.m1 := by
    rw [List.map_append, runSlot_map_fst, runSlot_map_fst, himg.1, himg.2.1]
  unfold metaOsBytes
  iintro ⟨H1, H2⟩
  isplitl [H1]
  · iexists _; iframe H1; ipureintro; exact hm
  · iexists _; iframe H2; ipureintro; exact hm

/-- The store slots' page-cache bytes. -/
theorem open_slotsOs (p : BFile) (xs : List ByteG) (S : List Nat) :
    ([∗list] s ∈ S, osBytes (GF := GF) p.ino (4096 * s) (DFrac.own 1) (runSlot xs s)) ⊢
      [∗list] s ∈ S, osSlot (GF := GF) p s (bytesAt (xs.map Prod.fst) (4096 * s) 4096) := by
  refine BigSepL.bigSepL_mono fun {_ s} _ => ?_
  unfold osSlot
  iintro H
  iexists _; iframe H; ipureintro; exact runSlot_map_fst xs s

/-- The writer's slots' page-cache bytes (those inside the file). -/
theorem open_wOs (p : BFile) (xs : List ByteG) (W : List Nat) :
    ([∗list] s ∈ W.filter (fun s => decide (4096 * s < xs.length)),
        osBytes (GF := GF) p.ino (4096 * s) (DFrac.own 1) (runSlot xs s)) ⊢
      wBytes (GF := GF) p W (fun s => bytesAt (xs.map Prod.fst) (4096 * s) 4096) xs.length := by
  refine (bigSepL_ite_filter (fun s => decide (4096 * s < xs.length))
    (fun s => osBytes (GF := GF) p.ino (4096 * s) (DFrac.own 1) (runSlot xs s)) W).2.trans ?_
  unfold wBytes
  refine BigSepL.bigSepL_mono fun {_ s} _ => ?_
  by_cases h : 4096 * s < xs.length
  · simp only [h, decide_true, ↓reduceIte]
    by_cases hf : 4096 * (s + 1) ≤ xs.length
    · simp only [hf, ↓reduceIte]
      iintro H; iexists _; iframe H; ipureintro; exact runSlot_map_fst xs s
    · simp only [hf, ↓reduceIte]
      iintro H; iexists _; iframe H; ipureintro
      rw [runSlot_map_fst, List.take_of_length_le]
      unfold bytesAt; simp only [List.length_take, List.length_drop, List.length_map]; omega
  · have hf : ¬ 4096 * (s + 1) ≤ xs.length := by omega
    simp only [h, hf, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact .rfl

/-- The metas' cells' two quarters, from slots 0 and 1. -/
theorem open_metaCells (b : Loc) (L : Nat) (C : CommitSt) (ys : List w8) (vf : Nat → val)
    (himg : fileImage ys C) (h8 : 8192 ≤ ys.length) :
    cellsR (GF := GF) b (4096 * 0) 4096 (openVf ys vf) ∗
      cellsR (GF := GF) b (4096 * 1) 4096 (openVf ys vf) ⊢
    metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, L)) C ∗
      metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, L)) C := by
  refine (sep_mono (open_slot_bytes b ys vf 0 (by omega))
    (open_slot_bytes b ys vf 1 (by omega))).trans ?_
  have e0 : b +ₗ ((4096 * 0 : Nat) : Int) = b := by simp
  have e1 : b +ₗ ((4096 * 1 : Nat) : Int) = b +ₗ (4096 : Int) := by simp
  rw [e0, e1, Nat.mul_zero, Nat.mul_one, ← himg.1, ← himg.2.1]
  simp only [metaCellsQ]
  iintro ⟨H0, H1⟩
  icases (bytes_quarters b C.m0).2 $$ H0 with ⟨H0, H0'⟩
  icases (bytes_quarters _ C.m1).2 $$ H1 with ⟨H1, H1'⟩
  iframe

/-- **`Open`'s carving**: the file `xs` (at least its two metas, at most the mapping `(b, L)`)
and the mapping's client halves, as `open_core`'s per-slot inputs. -/
theorem open_carve (p : BFile) (b : Loc) (L : Nat) (C : CommitSt) (xs : List ByteG)
    (vf : Nat → val) (himg : fileImage (xs.map Prod.fst) C) (htree : treeOK C)
    (hhwm : C.hwm * 4096 ≤ xs.length) (h8 : 8192 ≤ xs.length) (hL : xs.length ≤ L) :
    osBytes (GF := GF) p.ino 0 (DFrac.own 1) xs ∗
      bytesPointsto (GF := GF) b (DFrac.own (1 : Qp).half) (xs.map Prod.fst) ∗
      cellsR (GF := GF) b xs.length (L - xs.length) vf ⊢
    metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ∗
      metaOsBytes (GF := GF) p (DFrac.own (1 : Qp).half) C ∗
      ([∗list] s ∈ slotsOf C FLPg.empty,
        osSlot (GF := GF) p s (bytesAt (xs.map Prod.fst) (4096 * s) 4096)) ∗
      wBytes (GF := GF) p (wSlots (L / 4096) C FLPg.empty)
        (fun s => bytesAt (xs.map Prod.fst) (4096 * s) 4096) xs.length ∗
      metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, L)) C ∗
      metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, L)) C ∗
      ([∗list] s ∈ slotsOf C FLPg.empty,
        bytesPointsto (GF := GF) (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half)
          (bytesAt (xs.map Prod.fst) (4096 * s) 4096)) ∗
      wCells (GF := GF) (some (b, L)) (wSlots (L / 4096) C FLPg.empty) := by
  have hyl : (xs.map Prod.fst).length = xs.length := List.length_map ..
  have hslot := fun s hs => open_slot (xs.map Prod.fst) C htree (by omega) s hs
  have hSk : ∀ s ∈ slotsOf C FLPg.empty, 2 ≤ s ∧ s < L / 4096 := fun s hs => by
    have := hslot s hs
    exact ⟨this.1, by
      have : s + 1 ≤ C.hwm := this.2.1
      have : 4096 * (s + 1) ≤ L := by omega
      omega⟩
  have hSn : ∀ s ∈ slotsOf C FLPg.empty, 4096 * (s + 1) ≤ xs.length := by
    intro s hs; have := (hslot s hs).2.1; omega
  iintro ⟨Hos, Hb, Hc⟩
  -- the page-cache side
  ihave Hos := osBytes_slots p xs $$ Hos
  have hP := slots_partition (L / 4096) (slotsOf C FLPg.empty) (wSlots (L / 4096) C FLPg.empty)
    (by omega) (slotsOf_nodup _ _) (wSlots_nodup _ _ _) hSk (fun s => by rw [mem_wSlots])
  have hT : (0 :: 1 :: (slotsOf C FLPg.empty ++ (wSlots (L / 4096) C FLPg.empty).filter
      (fun s => decide (4096 * s < xs.length)))).Nodup := by
    have hsub : (0 :: 1 :: (slotsOf C FLPg.empty ++ (wSlots (L / 4096) C FLPg.empty).filter
        (fun s => decide (4096 * s < xs.length)))).Sublist
        (0 :: 1 :: (slotsOf C FLPg.empty ++ wSlots (L / 4096) C FLPg.empty)) :=
      ((List.filter_sublist).append_left _).cons_cons 1 |>.cons_cons 0
    exact hsub.nodup (hP.nodup_iff.2 List.nodup_range)
  ihave Hos := bigSepL_sub_nodup _ (List.range xs.length) hT ?_ $$ Hos
  · intro s hs
    rw [List.mem_range]
    simp only [List.mem_cons, List.mem_append, List.mem_filter, decide_eq_true_eq] at hs
    rcases hs with h | h | h | h
    · omega
    · omega
    · have := hSn s h; omega
    · omega
  icases BigSepL.bigSepL_cons.1 $$ Hos with ⟨H0, Hos⟩
  icases BigSepL.bigSepL_cons.1 $$ Hos with ⟨H1, Hos⟩
  icases BigSepL.bigSepL_append.1 $$ Hos with ⟨HSo, HWo⟩
  icases open_metaOs p C xs himg h8 $$ [H0 H1] with ⟨Hm1, Hm2⟩
  · iframe
  ihave HSo := open_slotsOs p xs _ $$ HSo
  ihave HWo := open_wOs p xs _ $$ HWo
  -- the cells' side
  rw [← hyl]
  ihave Hc := open_cells b (xs.map Prod.fst) L vf (by omega) $$ [Hb Hc]
  · iframe
  have e : L = 4096 * (L / 4096) + L % 4096 := (Nat.div_add_mod L 4096).symm
  have hsplit := cellsR_append (GF := GF) b 0 (4096 * (L / 4096)) (L % 4096)
    (openVf (xs.map Prod.fst) vf)
  rw [← e, Nat.zero_add] at hsplit
  icases hsplit.1 $$ Hc with ⟨Hc, Hp⟩
  ihave Hc := cellsR_slots b _ _ $$ Hc
  ihave Hc := (BigSepL.bigSepL_perm (Φ := fun s => cellsR (GF := GF) b (4096 * s) 4096
    (openVf (xs.map Prod.fst) vf)) hP).2 $$ Hc
  icases BigSepL.bigSepL_cons.1 $$ Hc with ⟨H0, Hc⟩
  icases BigSepL.bigSepL_cons.1 $$ Hc with ⟨H1, Hc⟩
  icases BigSepL.bigSepL_append.1 $$ Hc with ⟨HSc, HWc⟩
  icases open_metaCells b L C (xs.map Prod.fst) vf himg (by omega) $$ [H0 H1] with ⟨Hq1, Hq2⟩
  · iframe
  rw [hyl]
  iframe Hm1 Hm2 HSo HWo Hq1 Hq2
  isplitl [HSc]
  · iapply bigSepL_mono_mem' ?_ $$ HSc
    intro s hs
    exact open_slot_bytes b _ vf s (by rw [hyl]; exact hSn s hs)
  · unfold wCells
    isplitl [HWc]
    · iapply bigSepL_mono_mem' ?_ $$ HWc
      intro s hs
      have := ((mem_wSlots _ _ _ s).1 hs).2.1
      have h : 4096 * (s + 1) ≤ L := by omega
      simp only [h, ↓reduceIte]
      exact exists_intro (Ψ := fun vf => cellsR (GF := GF) b (4096 * s) 4096 vf) _
    · iexists _; iexact Hp

end carve

end bbolt
end EtcdGrove
end Perennial
