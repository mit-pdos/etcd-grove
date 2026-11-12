/-
The writer's `W` slots carved into `tx.write`'s target slots and back (batch 39 of
`notes/bbolt-proof-plan.md`, for `Commit`, U10): `wSlots_carve` takes the slots `S` (inside the
mapping and the file) out of `wdbLive`'s `wCells`/`wBytes` as `wrSlots` (`Commit/WriteDefs`), the
rest staying `W \ S`; `wSlots_return` puts them back after a failed write (their new bytes); and
`wrSlots_agree` (the list form of `cellsR_agree_bytes`) reads the written cells back as
`slotsOwn`, which `store_publish` takes.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteDefs
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

set_option linter.unusedSectionVars false

section bufsnd
variable [GooseExts]

private theorem flatMap_nodup_of {α β : Type} (f : α → List β) : ∀ (l : List α),
    (∀ a ∈ l, (f a).Nodup) → l.Pairwise (fun a b => ∀ x ∈ f a, x ∉ f b) → (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: t, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h2
    refine ⟨h1 a (List.mem_cons_self ..), flatMap_nodup_of f t (fun b hb => h1 b
      (List.mem_cons_of_mem _ hb)) ht, fun x hx y hy hxy => ?_⟩
    subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.1 hy
    exact ha b hb x hx hxb

/-- **The dirty pages' slots have no repeats** when no slot lies in two buffers' extents
(`bufsOK`'s and `spillBufs`' last clause, maintainer 12, item 4; the converse of
`Commit/WriteRun.bufSlots_disj`): `tx.write`'s `(bufSlots bufs).Nodup`. -/
theorem bufSlots_nodup_of_disj (bufs : GMap w64 (List w8))
    (h : ∀ id pg, bufs !! id = some pg → ∀ j < 1 + pageOverflow pg, ∀ id' pg',
      bufs !! id' = some pg' → ∀ j' < 1 + pageOverflow pg', id.toNat + j = id'.toNat + j' →
        id' = id) :
    (bufSlots bufs).Nodup := by
  unfold bufSlots
  refine flatMap_nodup_of _ _ (fun e _ => List.nodup_range' ..) ?_
  have hp : bufs.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
    List.pairwise_map.1 (GMap.toList_keys_nodup bufs)
  refine hp.imp_of_mem fun {a b} ha hb hne x hxa hxb => hne ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hxa
  obtain ⟨i', hi', he⟩ := List.mem_range'.1 hxb
  have hA := (GMap.mem_toList bufs a.1 a.2).1 ha
  have hB := (GMap.mem_toList bufs b.1 b.2).1 hb
  exact (h a.1 a.2 hA i hi b.1 b.2 hB i' hi' (by omega)).symm

end bufsnd

section wslots
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- `W`'s slots but `S`. -/
def wMinus (W S : List Nat) : List Nat := W.filter (fun s => decide (s ∉ S))

theorem mem_wMinus (W S : List Nat) (s : Nat) : s ∈ wMinus W S ↔ s ∈ W ∧ s ∉ S := by
  simp [wMinus]

/-- The per-slot body of `wCells`' list. -/
private abbrev wcF (b : Loc) (len : Nat) (s : Nat) : IProp GF :=
  if 4096 * (s + 1) ≤ len then iprop(∃ vf, cellsR b (4096 * s) 4096 vf) else iprop(emp)

/-- The per-slot body of `wBytes`. -/
private abbrev wbG (p : GoString) (wb : Nat → List w8) (size : Nat) (s : Nat) : IProp GF :=
  if 4096 * (s + 1) ≤ size then
    iprop(∃ xs : List ByteG, osBytes p.ino (4096 * s) (DFrac.own 1) xs ∗
      ⌜xs.map Prod.fst = wb s⌝)
  else if 4096 * s < size then
    iprop(∃ xs : List ByteG, osBytes p.ino (4096 * s) (DFrac.own 1) xs ∗
      ⌜xs.map Prod.fst = (wb s).take (size - 4096 * s)⌝)
  else iprop(emp)

omit hos in
private theorem wCells_eq (b : Loc) (len : Nat) (W : List Nat) :
    wCells (GF := GF) (some (b, len)) W ⊣⊢
      ([∗list] s ∈ W, wcF b len s) ∗ ∃ vf, cellsR b (4096 * (len / 4096)) (len % 4096) vf := by
  unfold wCells; exact .rfl

private theorem wBytes_eq (p : GoString) (W : List Nat) (wb : Nat → List w8) (size : Nat) :
    wBytes (GF := GF) p W wb size ⊣⊢ [∗list] s ∈ W, wbG p wb size s := by
  unfold wBytes; exact .rfl

/-- `W` split by membership in `S`. -/
private theorem perm_split (W S : List Nat) :
    W.Perm (W.filter (fun s => decide (s ∈ S)) ++ wMinus W S) := by
  have h := List.filter_append_perm (fun s => decide (s ∈ S)) W
  have he : (fun s => !decide (s ∈ S)) = (fun s => decide (s ∉ S)) := by
    funext s; simp
  rw [he] at h
  exact h.symm

/-- `S` (no duplicates, inside `W`) is a sub-multiset of `W`'s slots in `S`. -/
private theorem sub_split (W S : List Nat) (hnd : S.Nodup) (hsub : ∀ s ∈ S, s ∈ W) :
    ∃ T, (S ++ T).Perm (W.filter (fun s => decide (s ∈ S))) := by
  have hsp : S.Subperm (W.filter (fun s => decide (s ∈ S))) :=
    List.subperm_of_subset hnd (fun s hs => List.mem_filter.2 ⟨hsub s hs, by simpa using hs⟩)
  obtain ⟨l, hl, hls⟩ := hsp
  obtain ⟨T, hT⟩ := hls.exists_perm_append
  exact ⟨T, (hl.symm.append_right T).trans hT.symm⟩

private theorem bsplit {Φ : Nat → IProp GF} {l l1 l2 : List Nat} (h : l.Perm (l1 ++ l2)) :
    ([∗list] s ∈ l, Φ s) ⊢ ([∗list] s ∈ l1, Φ s) ∗ [∗list] s ∈ l2, Φ s :=
  (BigSepL.bigSepL_perm h).1.trans BigSepL.bigSepL_append.1

/-- **Carving the target slots out of the `W` slots**: `S` (no duplicates, `W` slots, each whole
inside the mapping and the file) as `wrSlots`, the rest `W \ S`. -/
theorem wSlots_carve (b : Loc) (len : Nat) (p : GoString) (W S : List Nat) (wb : Nat → List w8)
    (size : Nat) (hnd : S.Nodup) (hsub : ∀ s ∈ S, s ∈ W)
    (hin : ∀ s ∈ S, 4096 * (s + 1) ≤ len ∧ 4096 * (s + 1) ≤ size) :
    wCells (GF := GF) (some (b, len)) W ∗ wBytes p W wb size ⊢
      wrSlots b p S wb ∗ wCells (some (b, len)) (wMinus W S) ∗ wBytes p (wMinus W S) wb size := by
  obtain ⟨T, hT⟩ := sub_split W S hnd hsub
  have hW := perm_split W S
  iintro ⟨Hc, Hb⟩
  icases (wCells_eq (GF := GF) b len W).1 $$ Hc with ⟨Hc, Hpart⟩
  ihave Hb := (wBytes_eq (GF := GF) p W wb size).1 $$ Hb
  icases bsplit (Φ := wcF b len) hW $$ Hc with ⟨HcA, HcR⟩
  icases bsplit (Φ := wbG p wb size) hW $$ Hb with ⟨HbA, HbR⟩
  icases bsplit (Φ := wcF b len) hT.symm $$ HcA with ⟨HcS, -⟩
  icases bsplit (Φ := wbG p wb size) hT.symm $$ HbA with ⟨HbS, -⟩
  isplitl [HcS HbS]
  · unfold wrSlots
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [HbS]
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wbG (GF := GF) p wb size s)
        (Ψ := fun _ s => osSlot (GF := GF) p s (wb s)) ?_) $$ HbS
      intro k x hx
      have h := (hin x (List.mem_of_getElem? hx)).2
      simp only [wbG, h, ite_true, osSlot]
      exact .rfl
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wcF (GF := GF) b len s)
        (Ψ := fun _ s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf)) ?_) $$ HcS
      intro k x hx
      have h := (hin x (List.mem_of_getElem? hx)).1
      simp only [wcF, h, ite_true]
      exact .rfl
  isplitl [HcR Hpart]
  · iapply (wCells_eq (GF := GF) b len (wMinus W S)).2
    iframe
  · iapply (wBytes_eq (GF := GF) p (wMinus W S) wb size).2
    iexact HbR

/-- The bytes after a write to the slots `S`: `wb'` there, `wb` elsewhere. -/
def wbUpd (S : List Nat) (wb' wb : Nat → List w8) (s : Nat) : List w8 :=
  if s ∈ S then wb' s else wb s

/-- **Putting the target slots back** (after a failed write): `S ++ W'` (the same slots as `W` when
`W' = wMinus W S` and `S ⊆ W`), the slots of `S` holding their new bytes. -/
theorem wSlots_return (b : Loc) (len : Nat) (p : GoString) (W' S : List Nat)
    (wb wb' : Nat → List w8) (size : Nat) (hdisj : ∀ s ∈ W', s ∉ S)
    (hin : ∀ s ∈ S, 4096 * (s + 1) ≤ len ∧ 4096 * (s + 1) ≤ size) :
    wrSlots (GF := GF) b p S wb' ∗ wCells (some (b, len)) W' ∗ wBytes p W' wb size ⊢
      wCells (some (b, len)) (S ++ W') ∗ wBytes p (S ++ W') (wbUpd S wb' wb) size := by
  iintro ⟨Hs, Hc, Hb⟩
  unfold wrSlots
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hs with ⟨Ho, Hcs⟩
  icases (wCells_eq (GF := GF) b len W').1 $$ Hc with ⟨Hc, Hpart⟩
  ihave Hb := (wBytes_eq (GF := GF) p W' wb size).1 $$ Hb
  isplitl [Hcs Hc Hpart]
  · iapply (wCells_eq (GF := GF) b len (S ++ W')).2
    iframe Hpart
    iapply BigSepL.bigSepL_append.2
    iframe Hc
    iapply (BigSepL.bigSepL_mono (Φ := fun _ s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf))
        (Ψ := fun _ s => wcF (GF := GF) b len s) ?_) $$ Hcs
    intro k x hx
    have h := (hin x (List.mem_of_getElem? hx)).1
    simp only [wcF, h, ite_true]
    exact .rfl
  · iapply (wBytes_eq (GF := GF) p (S ++ W') (wbUpd S wb' wb) size).2
    iapply BigSepL.bigSepL_append.2
    isplitl [Ho]
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ s => osSlot (GF := GF) p s (wb' s))
        (Ψ := fun _ s => wbG (GF := GF) p (wbUpd S wb' wb) size s) ?_) $$ Ho
      intro k x hx
      have hm := List.mem_of_getElem? hx
      have h := (hin x hm).2
      simp only [wbG, h, ite_true, wbUpd, hm, osSlot]
      exact .rfl
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wbG (GF := GF) p wb size s)
        (Ψ := fun _ s => wbG (GF := GF) p (wbUpd S wb' wb) size s) ?_) $$ Hb
      intro k x hx
      have hm := hdisj x (List.mem_of_getElem? hx)
      have he : wbUpd S wb' wb x = wb x := by simp only [wbUpd, hm, ite_false]
      simp only [wbG, he]
      exact .rfl

/-! ### Slots relative to the file's size (maintainer 12, item 3: `Tx.write_ext`) -/

/-- **Slots relative to the file's size**: the slots `S` of the mapping at `b`, their page-cache
bytes below `size` as the writer side holds them (`wBytes`: a slot inside the file whole, the slot
across the end its part, a slot past the end nothing) and their mapped cells' client halves (any
values). `wrSlots` when every slot of `S` is inside the file (`wrSlotsSz_in`); what
`wSlots_carveSz` takes out of the writer's `W` slots without a size premise
(`Tx.write_ext.spec`). -/
def wrSlotsSz (b : Loc) (p : GoString) (S : List Nat) (wb : Nat → List w8) (size : Nat) :
    IProp GF :=
  iprop(wBytes p S wb size ∗ [∗list] s ∈ S, ∃ vf, cellsR b (4096 * s) 4096 vf)

theorem wrSlotsSz_app (b : Loc) (p : GoString) (S T : List Nat) (wb : Nat → List w8)
    (size : Nat) :
    wrSlotsSz (GF := GF) b p (S ++ T) wb size ⊣⊢ wrSlotsSz b p S wb size ∗ wrSlotsSz b p T wb size := by
  unfold wrSlotsSz wBytes
  constructor
  · iintro ⟨Hb, Hc⟩
    icases BigSepL.bigSepL_append.1 $$ Hb with ⟨Hb1, Hb2⟩
    icases BigSepL.bigSepL_append.1 $$ Hc with ⟨Hc1, Hc2⟩
    iframe
  · iintro ⟨⟨Hb1, Hc1⟩, ⟨Hb2, Hc2⟩⟩
    isplitl [Hb1 Hb2]
    · iapply BigSepL.bigSepL_append.2; iframe
    · iapply BigSepL.bigSepL_append.2; iframe

/-- `wrSlotsSz` only reads `wb` on its slots. -/
theorem wrSlotsSz_congr (b : Loc) (p : GoString) (S : List Nat) (wb wb' : Nat → List w8)
    (size : Nat) (h : ∀ s ∈ S, wb s = wb' s) :
    wrSlotsSz (GF := GF) b p S wb size ⊢ wrSlotsSz b p S wb' size := by
  unfold wrSlotsSz
  iintro ⟨Hb, Hc⟩
  iframe Hc
  ihave Hb := (wBytes_eq (GF := GF) p S wb size).1 $$ Hb
  iapply (wBytes_eq (GF := GF) p S wb' size).2
  iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wbG (GF := GF) p wb size s)
      (Ψ := fun _ s => wbG (GF := GF) p wb' size s) ?_) $$ Hb
  intro k x hx
  have he := h x (List.mem_of_getElem? hx)
  simp only [wbG, he]
  exact .rfl

/-- A slot inside the file at `size` is inside it at a larger `size'`, with the same bytes. -/
theorem wrSlotsSz_grow (b : Loc) (p : GoString) (S : List Nat) (wb : Nat → List w8)
    (size size' : Nat) (hle : size ≤ size') (hin : ∀ s ∈ S, 4096 * (s + 1) ≤ size) :
    wrSlotsSz (GF := GF) b p S wb size ⊢ wrSlotsSz b p S wb size' := by
  unfold wrSlotsSz
  iintro ⟨Hb, Hc⟩
  iframe Hc
  ihave Hb := (wBytes_eq (GF := GF) p S wb size).1 $$ Hb
  iapply (wBytes_eq (GF := GF) p S wb size').2
  iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wbG (GF := GF) p wb size s)
      (Ψ := fun _ s => wbG (GF := GF) p wb size' s) ?_) $$ Hb
  intro k x hx
  have h1 := hin x (List.mem_of_getElem? hx)
  have h2 : 4096 * (x + 1) ≤ size' := by omega
  simp only [wbG, h1, h2, ite_true]
  exact .rfl

/-- **`wrSlotsSz` of slots inside the file is `wrSlots`.** -/
theorem wrSlotsSz_in (b : Loc) (p : GoString) (S : List Nat) (wb : Nat → List w8) (size : Nat)
    (hin : ∀ s ∈ S, 4096 * (s + 1) ≤ size) :
    wrSlotsSz (GF := GF) b p S wb size ⊣⊢ wrSlots b p S wb := by
  have hb : wBytes (GF := GF) p S wb size ⊣⊢ [∗list] s ∈ S, osSlot p s (wb s) := by
    refine (wBytes_eq (GF := GF) p S wb size).trans ⟨BigSepL.bigSepL_mono fun hx => ?_,
      BigSepL.bigSepL_mono fun hx => ?_⟩
    · have h := hin _ (List.mem_of_getElem? hx)
      simp only [wbG, h, ite_true, osSlot]
      exact .rfl
    · have h := hin _ (List.mem_of_getElem? hx)
      simp only [wbG, h, ite_true, osSlot]
      exact .rfl
  unfold wrSlotsSz wrSlots
  exact (sep_congr hb .rfl).trans BigSepL.bigSepL_sep_eqv.symm

/-- **Carving the target slots out of the `W` slots, at the file's size**: `S` (no duplicates,
`W` slots, each whole inside the mapping, anywhere relative to the file) as `wrSlotsSz`, the rest
`W \ S`. -/
theorem wSlots_carveSz (b : Loc) (len : Nat) (p : GoString) (W S : List Nat) (wb : Nat → List w8)
    (size : Nat) (hnd : S.Nodup) (hsub : ∀ s ∈ S, s ∈ W) (hin : ∀ s ∈ S, 4096 * (s + 1) ≤ len) :
    wCells (GF := GF) (some (b, len)) W ∗ wBytes p W wb size ⊢
      wrSlotsSz b p S wb size ∗ wCells (some (b, len)) (wMinus W S) ∗ wBytes p (wMinus W S) wb size := by
  obtain ⟨T, hT⟩ := sub_split W S hnd hsub
  have hW := perm_split W S
  iintro ⟨Hc, Hb⟩
  icases (wCells_eq (GF := GF) b len W).1 $$ Hc with ⟨Hc, Hpart⟩
  ihave Hb := (wBytes_eq (GF := GF) p W wb size).1 $$ Hb
  icases bsplit (Φ := wcF b len) hW $$ Hc with ⟨HcA, HcR⟩
  icases bsplit (Φ := wbG p wb size) hW $$ Hb with ⟨HbA, HbR⟩
  icases bsplit (Φ := wcF b len) hT.symm $$ HcA with ⟨HcS, -⟩
  icases bsplit (Φ := wbG p wb size) hT.symm $$ HbA with ⟨HbS, -⟩
  isplitl [HcS HbS]
  · unfold wrSlotsSz
    isplitl [HbS]
    · iapply (wBytes_eq (GF := GF) p S wb size).2; iexact HbS
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wcF (GF := GF) b len s)
        (Ψ := fun _ s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf)) ?_) $$ HcS
      intro k x hx
      have h := hin x (List.mem_of_getElem? hx)
      simp only [wcF, h, ite_true]
      exact .rfl
  isplitl [HcR Hpart]
  · iapply (wCells_eq (GF := GF) b len (wMinus W S)).2
    iframe
  · iapply (wBytes_eq (GF := GF) p (wMinus W S) wb size).2
    iexact HbR

/-- **Putting slots back at the file's (new) size** (after `Tx.write_ext`: the failed write's
slots, or the tail on success): `S ++ W'`, the slots of `S` holding their new bytes `wb'`; the
other slots `W'` lie inside the old file (`size ≤ size'`). -/
theorem wSlots_returnSz (b : Loc) (len : Nat) (p : GoString) (W' S : List Nat)
    (wb wb' : Nat → List w8) (size size' : Nat) (hdisj : ∀ s ∈ W', s ∉ S)
    (hinS : ∀ s ∈ S, 4096 * (s + 1) ≤ len) (hinW : ∀ s ∈ W', 4096 * (s + 1) ≤ size)
    (hle : size ≤ size') :
    wrSlotsSz (GF := GF) b p S wb' size' ∗ wCells (some (b, len)) W' ∗ wBytes p W' wb size ⊢
      wCells (some (b, len)) (S ++ W') ∗ wBytes p (S ++ W') (wbUpd S wb' wb) size' := by
  unfold wrSlotsSz
  iintro ⟨⟨Ho, Hcs⟩, Hc, Hb⟩
  icases (wCells_eq (GF := GF) b len W').1 $$ Hc with ⟨Hc, Hpart⟩
  ihave Hb := (wBytes_eq (GF := GF) p W' wb size).1 $$ Hb
  ihave Ho := (wBytes_eq (GF := GF) p S wb' size').1 $$ Ho
  isplitl [Hcs Hc Hpart]
  · iapply (wCells_eq (GF := GF) b len (S ++ W')).2
    iframe Hpart
    iapply BigSepL.bigSepL_append.2
    iframe Hc
    iapply (BigSepL.bigSepL_mono (Φ := fun _ s => iprop(∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf))
        (Ψ := fun _ s => wcF (GF := GF) b len s) ?_) $$ Hcs
    intro k x hx
    have h := hinS x (List.mem_of_getElem? hx)
    simp only [wcF, h, ite_true]
    exact .rfl
  · iapply (wBytes_eq (GF := GF) p (S ++ W') (wbUpd S wb' wb) size').2
    iapply BigSepL.bigSepL_append.2
    isplitl [Ho]
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wbG (GF := GF) p wb' size' s)
        (Ψ := fun _ s => wbG (GF := GF) p (wbUpd S wb' wb) size' s) ?_) $$ Ho
      intro k x hx
      have hm := List.mem_of_getElem? hx
      have he : wbUpd S wb' wb x = wb' x := by simp only [wbUpd, hm, ite_true]
      simp only [wbG, he]
      exact .rfl
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ s => wbG (GF := GF) p wb size s)
        (Ψ := fun _ s => wbG (GF := GF) p (wbUpd S wb' wb) size' s) ?_) $$ Hb
      intro k x hx
      have hm := List.mem_of_getElem? hx
      have he : wbUpd S wb' wb x = wb x := by simp only [wbUpd, hdisj x hm, ite_false]
      have h1 := hinW x hm
      have h2 : 4096 * (x + 1) ≤ size' := by omega
      simp only [wbG, he, h1, h2, ite_true]
      exact .rfl

section agree
variable [sem : go.Semantics] {s : Stuckness} {E : CoPset}

/-- **The written slots read back** (the list form of `cellsR_agree_bytes`): `wrSlots` whose
page-cache bytes are whole pages inside the mapping `b` are `slotsOwn`, around any step `e`. -/
theorem wrSlots_agree (e : Expr) (htv : toVal e = none) (p : GoString) (dqm : DFrac) (m : OsMeta)
    (b : Loc) (len : Nat) (hb : m.maps !! b = some len) (hE : ↑osN ⊆ E) (wb : Nat → List w8)
    (Φ : val → IProp GF) :
    ∀ (S : List Nat), (∀ t ∈ S, 4096 * (t + 1) ≤ len ∧ (wb t).length = 4096) →
    ⊢ osInv (GF := GF) -∗ osMeta p.ino dqm m -∗ wrSlots b p S wb -∗
      (osMeta p.ino dqm m -∗ slotsOwn (some (b, len)) p S wb -∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }}
  | [], _ => by
    iintro #Hinv Hm _ HΦ
    iapply HΦ $$ Hm
    unfold slotsOwn
    iapply BigSepL.bigSepL_nil.2; iempintro
  | t :: S, hS => by
    iintro #Hinv Hm Hs HΦ
    unfold wrSlots
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨⟨Hx, %vf, Hcx⟩, Hs⟩
    icases (show osSlot (GF := GF) p t (wb t) ⊢ ∃ xs : List ByteG,
        osBytes p.ino (4096 * t) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = wb t⌝ by
        unfold osSlot; exact .rfl) $$ Hx with ⟨%xs, Hx, %Hxs⟩
    obtain ⟨ht1, ht2⟩ := hS t (List.mem_cons_self ..)
    have hxl : xs.length = 4096 := by rw [← ht2, ← Hxs, List.length_map]
    have hc : cellsR (GF := GF) b (4096 * t) 4096 vf ⊢ cellsR b (4096 * t) xs.length vf := by
      rw [hxl]
    ihave Hcx := hc $$ Hcx
    iapply cellsR_agree_bytes e htv p dqm m b len hb (DFrac.own 1) hE Φ xs (4096 * t) vf
      (by omega) $$ Hinv Hm Hx Hcx
    iintro Hm Hx Hcx
    ihave Hcx := cellsR_bytes b (xs.map Prod.fst) (4096 * t) $$ [Hcx]
    · simp only [List.length_map]; iexact Hcx
    iapply wrSlots_agree e htv p dqm m b len hb hE wb Φ S
      (fun u hu => hS u (List.mem_cons_of_mem _ hu)) $$ Hinv Hm [Hs]
    · unfold wrSlots; iexact Hs
    iintro Hm Ho
    iapply HΦ $$ Hm
    unfold slotsOwn
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hx Hcx]
    · rw [Hxs]
      iframe Hcx
      iapply (show (∃ xs : List ByteG, osBytes p.ino (4096 * t) (DFrac.own 1) xs ∗
          ⌜xs.map Prod.fst = wb t⌝) ⊢ osSlot (GF := GF) p t (wb t) by unfold osSlot; exact .rfl)
      iexists xs; iframe; ipureintro; exact Hxs
    · iexact Ho

end agree

end wslots

end bbolt
end EtcdGrove
end Perennial
