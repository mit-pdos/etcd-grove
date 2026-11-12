/-
`tx.write()`'s slots and runs (U10c, `notes/bbolt-proof-plan.md`): a page's slots holding anything
(`slotAny`: some 4096 bytes of the page cache, any cells) as one run of the file's bytes and of the
mapping's cells over the page's extent (`slotsAny_run`), and back; a written run (bytes whose
first components are the page's, the cells' client halves holding them) as the page's slots, each
with its chunk (`run_done`); the slots of the dirty pages without repeats (`slotsAny_nodup`, from
their exclusive page-cache bytes) and therefore disjoint extents (`bufSlots_disj`); and the
assembly of the slots of all pages into the spec's `wrSlots`/`slotsOwn` with one function
(`bigSepL_choose`, `err_final`, `done_final`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteDefs
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.go_etcd_io.bbolt.Spill.PageBuf
public import Proof.os.WriteChunks

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The extent of the page `k` of `bufs` (its first slot and its overflow's). -/
def extB (bufs : GMap w64 (List w8)) (k : w64) : List Nat :=
  List.range' k.toNat (1 + pageOverflow ((bufs !! k).getD []))

theorem wr_flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `bufSlots`, over the keys. -/
theorem bufSlots_keys (bufs : GMap w64 (List w8)) :
    bufSlots bufs = (bufs.toList.map Prod.fst).flatMap (extB bufs) := by
  unfold bufSlots
  rw [List.flatMap_map]
  apply wr_flatMap_congr
  intro e he
  have h := (GMap.mem_toList bufs e.1 e.2).1 he
  unfold extB
  rw [h]; rfl

/-- `bufSlots`, over any order of the keys. -/
theorem bufSlots_perm (bufs : GMap w64 (List w8)) (ks : List w64)
    (hk : ks.Perm (bufs.toList.map Prod.fst)) :
    (ks.flatMap (extB bufs)).Perm (bufSlots bufs) := by
  rw [bufSlots_keys]
  exact hk.flatMap_right _

/-- A list of exactly the keys of `bufs` (without repeats) is a permutation of `toList`'s. -/
theorem keys_perm (bufs : GMap w64 (List w8)) (ks : List w64) (hnd : ks.Nodup)
    (hk : ∀ k, k ∈ ks ↔ (bufs !! k).isSome) :
    ks.Perm (bufs.toList.map Prod.fst) := by
  refine (List.perm_ext_iff_of_nodup hnd (GMap.toList_keys_nodup bufs)).2 fun k => ?_
  rw [hk k]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    exact List.mem_map.2 ⟨(k, v), (GMap.mem_toList bufs k v).2 hv, rfl⟩
  · intro h
    obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.1 h
    have := (GMap.mem_toList bufs k' v).1 hm
    simp [this]

theorem flatMap_nodup_disj {α : Type} {l : List α} {f : α → List Nat}
    (hnd : (l.flatMap f).Nodup) {a a' : α} (ha : a ∈ l) (ha' : a' ∈ l) (hne : a ≠ a') {x : Nat}
    (hx : x ∈ f a) (hx' : x ∈ f a') : False := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨-, hnd2, hdis⟩ := hnd
    rcases List.mem_cons.1 ha with h1 | hb
    · subst h1
      rcases List.mem_cons.1 ha' with h2 | hb'
      · exact hne h2.symm
      · exact hdis x hx x (List.mem_flatMap.2 ⟨a', hb', hx'⟩) rfl
    · rcases List.mem_cons.1 ha' with h2 | hb'
      · subst h2
        exact hdis x hx' x (List.mem_flatMap.2 ⟨a, hb, hx⟩) rfl
      · exact ih hnd2 hb hb'

/-- **The dirty pages' extents are disjoint** when their slots have no repeats. -/
theorem bufSlots_disj (bufs : GMap w64 (List w8)) (hnd : (bufSlots bufs).Nodup)
    {id id' : w64} {pg pg' : List w8} {j j' : Nat} (h1 : bufs !! id = some pg)
    (h2 : bufs !! id' = some pg') (hj : j < 1 + pageOverflow pg)
    (hj' : j' < 1 + pageOverflow pg') (he : id.toNat + j = id'.toNat + j') : id = id' := by
  refine Classical.byContradiction fun hne => ?_
  unfold bufSlots at hnd
  exact flatMap_nodup_disj hnd ((GMap.mem_toList _ _ _).2 h1) ((GMap.mem_toList _ _ _).2 h2)
    (fun h => hne (congrArg Prod.fst h)) (x := id.toNat + j) (by simp; omega) (by simp; omega)

theorem pageChunk_succ (P : List w8) (j : Nat) :
    pageChunk (P.drop 4096) j = pageChunk P (j + 1) := by
  unfold pageChunk
  rw [List.drop_drop]
  congr 2
  omega

theorem pageChunk_length (P : List w8) (c j : Nat) (hl : P.length = 4096 * c) (hj : j < c) :
    (pageChunk P j).length = 4096 := by
  unfold pageChunk
  simp only [List.length_take, List.length_drop]
  have : 4096 * j + 4096 ≤ 4096 * c := by omega
  omega

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The client halves of the cells `[lo, lo + n)` of the mapping at `b`, holding anything. -/
def cAny (b : Loc) (lo n : Nat) : IProp GF := iprop(∃ vf, cellsR b lo n vf)

/-- The page-cache bytes `[lo, lo + n)` of the file `p`, whole, holding anything. -/
def oAny (p : GoString) (lo n : Nat) : IProp GF :=
  iprop(∃ xs : List ByteG, osBytes p.ino lo (DFrac.own 1) xs ∗ ⌜xs.length = n⌝)

/-- A slot of a write, holding anything: some 4096 bytes in the page cache, any cells. -/
def slotAny (b : Loc) (p : GoString) (s : Nat) : IProp GF :=
  iprop(∃ bs : List w8, ⌜bs.length = 4096⌝ ∗ osSlot p s bs ∗ cAny b (4096 * s) 4096)

/-- A slot written with `a`: its cells' client halves and its page-cache bytes hold `a`
(`slotsOwn`'s per-slot resource). -/
def slotDone (b : Loc) (p : GoString) (s : Nat) (a : List w8) : IProp GF :=
  iprop(bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) a ∗ osSlot p s a)

theorem cAny_app (b : Loc) (lo n1 n2 : Nat) :
    cAny (GF := GF) b lo (n1 + n2) ⊣⊢ cAny b lo n1 ∗ cAny b (lo + n1) n2 := by
  unfold cAny
  constructor
  · iintro ⟨%vf, H⟩
    icases (cellsR_append b lo n1 n2 vf).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists vf; iexact H1
    · iexists vf; iexact H2
  · exact cellsR_join b lo n1 n2

theorem oAny_app (p : GoString) (lo n1 n2 : Nat) :
    oAny (GF := GF) p lo (n1 + n2) ⊣⊢ oAny p lo n1 ∗ oAny p (lo + n1) n2 := by
  unfold oAny
  constructor
  · iintro ⟨%xs, H, %hl⟩
    icases (osBytes_take_drop p lo _ xs n1 (by omega)).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists _; iframe H1; ipureintro; simp only [List.length_take]; omega
    · iexists _; iframe H2; ipureintro; simp only [List.length_drop]; omega
  · iintro ⟨⟨%xs, H1, %h1⟩, ⟨%ys, H2, %h2⟩⟩
    have e := osBytes_take_drop (GF := GF) p lo (DFrac.own 1) (xs ++ ys) xs.length (by simp)
    rw [List.take_left, List.drop_left, h1] at e
    iexists xs ++ ys
    isplitl [H1 H2]
    · iapply e.2; iframe
    · ipureintro; simp only [List.length_append]; omega

theorem oAny_zero (p : GoString) (lo : Nat) : ⊢ oAny (GF := GF) p lo 0 := by
  unfold oAny
  iexists []
  isplitl
  · iapply (osBytes_nil' (GF := GF) p lo _).2; iempintro
  · ipureintro; rfl

theorem cAny_zero (b : Loc) (lo : Nat) : ⊢ cAny (GF := GF) b lo 0 := by
  unfold cAny cellsR
  iexists (fun _ => LitV LitUnit)
  simp only [List.range'_zero]
  iapply BigSepL.bigSepL_nil.2; iempintro

theorem slotAny_run (b : Loc) (p : GoString) (s : Nat) :
    slotAny (GF := GF) b p s ⊣⊢ oAny p (4096 * s) 4096 ∗ cAny b (4096 * s) 4096 := by
  unfold slotAny oAny osSlot
  constructor
  · iintro ⟨%bs, %hl, ⟨%xs, H, %hx⟩, Hc⟩
    iframe Hc
    iexists xs
    iframe H
    ipureintro
    rw [← hl, ← hx, List.length_map]
  · iintro ⟨⟨%xs, H, %hl⟩, Hc⟩
    iexists xs.map Prod.fst
    isplitr
    · ipureintro; rw [List.length_map, hl]
    isplitl [H]
    · iexists xs; iframe H; ipureintro; rfl
    · iexact Hc

/-- **A page's slots holding anything are a run** of the page cache and of the cells. -/
theorem slotsAny_run (b : Loc) (p : GoString) : ∀ (c k : Nat),
    ([∗list] s ∈ List.range' k c, slotAny (GF := GF) b p s) ⊣⊢
      oAny p (4096 * k) (4096 * c) ∗ cAny b (4096 * k) (4096 * c)
  | 0, k => by
    simp only [List.range'_zero, Nat.mul_zero]
    constructor
    · iintro -
      isplitl
      · iapply oAny_zero
      · iapply cAny_zero
    · iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | c + 1, k => by
    have IH := slotsAny_run b p c (k + 1)
    rw [show 4096 * (k + 1) = 4096 * k + 4096 by omega] at IH
    rw [List.range'_succ, show 4096 * (c + 1) = 4096 + 4096 * c by omega]
    have A := oAny_app (GF := GF) p (4096 * k) 4096 (4096 * c)
    have C := cAny_app (GF := GF) b (4096 * k) 4096 (4096 * c)
    have S := slotAny_run (GF := GF) b p k
    constructor
    · iintro H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
      icases S.1 $$ H1 with ⟨Ho1, Hc1⟩
      icases IH.1 $$ H2 with ⟨Ho2, Hc2⟩
      isplitl [Ho1 Ho2]
      · iapply A.2; iframe
      · iapply C.2; iframe
    · iintro ⟨Ho, Hc⟩
      icases A.1 $$ Ho with ⟨Ho1, Ho2⟩
      icases C.1 $$ Hc with ⟨Hc1, Hc2⟩
      iapply BigSepL.bigSepL_cons.2
      isplitl [Ho1 Hc1]
      · iapply S.2; iframe
      · iapply IH.2; iframe

/-- The target slots of the spec, as slots holding anything. -/
theorem wrSlots_any (b : Loc) (p : GoString) (S : List Nat) (wb : Nat → List w8)
    (h : ∀ s ∈ S, (wb s).length = 4096) :
    wrSlots (GF := GF) b p S wb ⊢ [∗list] s ∈ S, slotAny b p s := by
  unfold wrSlots
  apply BigSepL.bigSepL_mono
  intro k s hk
  unfold slotAny cAny
  iintro ⟨Hs, Hc⟩
  iexists wb s
  isplitr
  · ipureintro; exact h s (List.mem_of_getElem? hk)
  iframe

/-- A written slot, as a slot holding anything. -/
theorem slotDone_any (b : Loc) (p : GoString) (s : Nat) (a : List w8) (h : a.length = 4096) :
    slotDone (GF := GF) b p s a ⊢ slotAny b p s := by
  unfold slotDone slotAny cAny
  iintro ⟨Hb, Hs⟩
  iexists a
  isplitr
  · ipureintro; exact h
  iframe Hs
  ihave Hc := bytes_cellsR b a (4096 * s) $$ Hb
  rw [h]
  iexists _; iexact Hc

/-- A byte points-to cut at `n`. -/
theorem bytes_cut (l : Loc) (lo : Nat) (dq : DFrac) (P : List w8) (n : Nat) (h : n ≤ P.length) :
    bytesPointsto (GF := GF) (l +ₗ ((lo : Nat) : Int)) dq P ⊣⊢
      bytesPointsto (l +ₗ ((lo : Nat) : Int)) dq (P.take n) ∗
        bytesPointsto (l +ₗ ((lo + n : Nat) : Int)) dq (P.drop n) := by
  have a := bytesPointsto_app (GF := GF) (l +ₗ ((lo : Nat) : Int)) dq (P.take n) (P.drop n)
  rw [List.take_append_drop] at a
  have e : ((lo : Nat) : Int) + (((P.take n).length : Nat) : Int) = ((lo + n : Nat) : Int) := by
    rw [List.length_take, Nat.min_eq_left h]; push_cast; rfl
  rw [loc_add_assoc, e] at a
  exact a

/-- **A written run is the page's slots**, each holding its chunk. -/
theorem run_done (b : Loc) (p : GoString) : ∀ (c k : Nat) (P : List w8) (ys : List ByteG),
    ys.map Prod.fst = P → P.length = 4096 * c →
    osBytes (GF := GF) p.ino (4096 * k) (DFrac.own 1) ys ∗
      bytesPointsto (b +ₗ ((4096 * k : Nat) : Int)) (DFrac.own (1 : Qp).half) P ⊢
    [∗list] s ∈ List.range' k c, slotDone b p s (pageChunk P (s - k))
  | 0, k, P, ys, _, _ => by
    iintro -; simp only [List.range'_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  | c + 1, k, P, ys, hy, hl => by
    rw [List.range'_succ]
    have hyl : ys.length = P.length := by rw [← hy, List.length_map]
    have Hos := osBytes_take_drop (GF := GF) p (4096 * k) (DFrac.own 1) ys 4096 (by omega)
    rw [show 4096 * k + 4096 = 4096 * (k + 1) by omega] at Hos
    have Hb := bytes_cut (GF := GF) b (4096 * k) (DFrac.own (1 : Qp).half) P 4096 (by omega)
    rw [show 4096 * k + 4096 = 4096 * (k + 1) by omega] at Hb
    have IH := run_done b p c (k + 1) (P.drop 4096) (ys.drop 4096)
      (by rw [List.map_drop, hy]) (by simp only [List.length_drop]; omega)
    have Hm : ([∗list] s ∈ List.range' (k + 1) c,
        slotDone (GF := GF) b p s (pageChunk (P.drop 4096) (s - (k + 1)))) ⊢
        [∗list] s ∈ List.range' (k + 1) c, slotDone b p s (pageChunk P (s - k)) := by
      apply BigSepL.bigSepL_mono
      intro i s hs
      have hm := List.mem_range'_1.1 (List.mem_of_getElem? hs)
      rw [show s - k = (s - (k + 1)) + 1 by omega, ← pageChunk_succ]
      try exact .rfl
    iintro ⟨Hy, HP⟩
    icases Hos.1 $$ Hy with ⟨Hy1, Hy2⟩
    icases Hb.1 $$ HP with ⟨HP1, HP2⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hy1 HP1]
    · unfold slotDone osSlot
      have hc0 : pageChunk P (k - k) = P.take 4096 := by simp [pageChunk]
      rw [hc0]
      iframe HP1
      iexists ys.take 4096
      iframe Hy1
      ipureintro; rw [List.map_take, hy]
    · iapply Hm
      iapply IH
      iframe

/-- Two slots holding anything are not the same slot. -/
theorem slotAny_excl (b : Loc) (p : GoString) (s : Nat) :
    slotAny (GF := GF) b p s ∗ slotAny b p s ⊢ False := by
  unfold slotAny osSlot
  iintro ⟨⟨%a1, %h1, ⟨%x1, H1, %hx1⟩, -⟩, ⟨%a2, %h2, ⟨%x2, H2, %hx2⟩, -⟩⟩
  have hl1 : x1.length = 4096 := by rw [← h1, ← hx1, List.length_map]
  have hl2 : x2.length = 4096 := by rw [← h2, ← hx2, List.length_map]
  obtain ⟨y1, z1, rfl⟩ : ∃ y z, x1 = y :: z := by
    cases x1 with
    | nil => simp at hl1
    | cons y z => exact ⟨y, z, rfl⟩
  obtain ⟨y2, z2, rfl⟩ : ∃ y z, x2 = y :: z := by
    cases x2 with
    | nil => simp at hl2
    | cons y z => exact ⟨y, z, rfl⟩
  icases (osBytes_cons' (GF := GF) p _ _ y1 z1).1 $$ H1 with ⟨H1, -⟩
  icases (osBytes_cons' (GF := GF) p _ _ y2 z2).1 $$ H2 with ⟨H2, -⟩
  unfold osByte
  icases gElem_valid_2 _ _ _ _ _ y1 y2 $$ H1 H2 with %Hv
  exact (dfrac_own_one_op_invalid _ Hv.1).elim

/-- **Slots holding anything have no repeats.** -/
theorem slotsAny_nodup (b : Loc) (p : GoString) : ∀ S : List Nat,
    ([∗list] s ∈ S, slotAny (GF := GF) b p s) ⊢ ⌜S.Nodup⌝
  | [] => by iintro -; ipureintro; exact List.nodup_nil
  | s :: S => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hs, H⟩
    by_cases hs : s ∈ S
    · icases BigSepL.bigSepL_mem_acc hs $$ H with ⟨Hs2, -⟩
      iexfalso
      iapply slotAny_excl b p s
      iframe
    · ihave %Hn := slotsAny_nodup b p S $$ H
      ipureintro; exact List.nodup_cons.2 ⟨hs, Hn⟩

/-- **One function for slots without repeats**, each holding its own value. -/
theorem bigSepL_choose {A : Type} [Inhabited A] (Ψ : Nat → A → IProp GF) :
    ∀ S : List Nat, S.Nodup →
    ([∗list] s ∈ S, ∃ a, Ψ s a) ⊢ ∃ f : Nat → A, [∗list] s ∈ S, Ψ s (f s)
  | [], _ => by
    iintro -; iexists (fun _ => default); iapply BigSepL.bigSepL_nil.2; iempintro
  | s :: S, hnd => by
    have hs : s ∉ S := (List.nodup_cons.1 hnd).1
    have IH := bigSepL_choose Ψ S (List.nodup_cons.1 hnd).2
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%a, Ha⟩, H⟩
    icases IH $$ H with ⟨%f, H⟩
    have Hm : ([∗list] t ∈ S, Ψ t (f t)) ⊢
        [∗list] t ∈ S, Ψ t ((fun t => if t = s then a else f t) t) := by
      apply BigSepL.bigSepL_mono
      intro i t ht
      have hne : t ≠ s := fun h => hs (h ▸ List.mem_of_getElem? ht)
      simp only [hne, ite_false]
      try exact .rfl
    iexists (fun t => if t = s then a else f t)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · simp only [ite_true]; iexact Ha
    · iapply Hm; iexact H

/-- The pure parts of a big separating conjunction, out. -/
theorem bigSepL_pure_out (S : List Nat) (φ : Nat → Prop) (X : Nat → IProp GF) :
    ([∗list] s ∈ S, ⌜φ s⌝ ∗ X s) ⊢ ⌜∀ s ∈ S, φ s⌝ ∗ [∗list] s ∈ S, X s := by
  refine BigSepL.bigSepL_sep_eqv.1.trans (sep_mono ?_ .rfl)
  refine (BigSepL.bigSepL_pure (φ := fun _ s => φ s)).1.trans ?_
  apply pure_mono
  intro h s hs
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hs
  exact h i s hi

/-- A big separating conjunction over a map, as one over a list of exactly its keys (the
`kvreconf` example's `bigSepM_keys`). -/
theorem wr_bigSepM_keys {V : Type} (Φ : w64 → V → IProp GF) (keys : List w64) :
    ∀ (m : GMap w64 V), keys.Nodup → (∀ k, k ∈ keys ↔ (m !! k).isSome) →
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗list] k ∈ keys, ∃ x, ⌜m !! k = some x⌝ ∗ Φ k x := by
  induction keys with
  | nil =>
    intro m _ hk
    have hm : m = ∅ := by
      apply GMap.ext; intro k
      have := hk k
      simp only [List.not_mem_nil, false_iff] at this
      cases h : m !! k with
      | none => rfl
      | some _ => simp [h] at this
    subst hm
    iintro -
    iapply (BigSepL.bigSepL_nil).2; iempintro
  | cons k keys IH =>
    intro m hnd hk
    have hk0 : k ∉ keys := (List.nodup_cons.mp hnd).1
    obtain ⟨x, hx⟩ : ∃ x, m !! k = some x := by
      have := (hk k).1 List.mem_cons_self
      cases h : m !! k with
      | none => simp [h] at this
      | some x => exact ⟨x, rfl⟩
    have hk' : ∀ k', k' ∈ keys ↔ (GMap.delete k m !! k').isSome := by
      intro k'
      by_cases hkk : k = k'
      · subst hkk; simp [hk0]
      · rw [GMap.lookup_delete_ne _ hkk, ← hk k']
        simp [List.mem_cons, Ne.symm hkk]
    iintro H
    ihave ⟨H1, H2⟩ := (BigSepM.bigSepM_delete (Φ := Φ) (m := m) hx).1 $$ H
    iapply (BigSepL.bigSepL_cons (Φ := fun _ k => iprop(∃ x, ⌜m !! k = some x⌝ ∗ Φ k x))).2
    isplitl [H1]
    · iexists x; iframe H1; ipureintro; exact hx
    ihave H2 := IH (GMap.delete k m) (List.nodup_cons.mp hnd).2 hk' $$ H2
    iapply (BigSepL.bigSepL_mono (Φ := fun _ k' => iprop(∃ x, ⌜GMap.delete k m !! k' = some x⌝ ∗
      Φ k' x)) ?_) $$ H2
    intro j k' hj
    have hne : k ≠ k' := fun h => hk0 (h ▸ List.mem_of_getElem? hj)
    iintro ⟨%x', %h', H⟩
    iexists x'; iframe H; ipureintro
    rw [GMap.lookup_delete_ne _ hne] at h'; exact h'

/-- **The target slots, per key**: their slots have no repeats, and each page's slots hold
anything. -/
theorem wr_start (b : Loc) (p : GoString) (bufs : GMap w64 (List w8)) (wb : Nat → List w8)
    (keys : List w64) (hnd : keys.Nodup) (hk : ∀ k, k ∈ keys ↔ (bufs !! k).isSome)
    (hwb : ∀ s ∈ bufSlots bufs, (wb s).length = 4096) :
    wrSlots (GF := GF) b p (bufSlots bufs) wb ⊢ ⌜(bufSlots bufs).Nodup⌝ ∗
      [∗list] k ∈ keys, ∃ pg, ⌜bufs !! k = some pg⌝ ∗
        [∗list] s ∈ List.range' k.toNat (1 + pageOverflow pg), slotAny b p s := by
  refine (wrSlots_any b p _ wb hwb).trans ?_
  refine (persistent_entails_right (slotsAny_nodup b p _)).trans (sep_mono .rfl ?_)
  refine Entails.trans ?_ (wr_bigSepM_keys (fun k pg =>
    iprop([∗list] s ∈ List.range' k.toNat (1 + pageOverflow pg), slotAny (GF := GF) b p s))
    keys bufs hnd hk)
  unfold bufSlots
  rw [BigSepL.bigSepL_flatMap]
  exact (BigSepM.bigSepM_toList (PROP := IProp GF) (M := GMap w64) (m := bufs)
    (Φ := fun k pg => iprop([∗list] s ∈ List.range' k.toNat (1 + pageOverflow pg),
      slotAny (GF := GF) b p s))).2

/-- **On an error**: every page's slots holding anything are the spec's `wrSlots`. -/
theorem err_final (b : Loc) (p : GoString) (bufs : GMap w64 (List w8))
    (L : List (w64 × Loc × List w8)) (hperm : (L.map Prod.fst).Perm (bufs.toList.map Prod.fst))
    (hmem : ∀ e ∈ L, bufs !! e.1 = some e.2.2) :
    ([∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
        slotAny (GF := GF) b p s) ⊢
      ∃ wb' : Nat → List w8, ⌜∀ s ∈ bufSlots bufs, (wb' s).length = 4096⌝ ∗
        wrSlots b p (bufSlots bufs) wb' := by
  have e1 : ([∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
      slotAny (GF := GF) b p s) ⊢ [∗list] s ∈ bufSlots bufs, slotAny b p s := by
    refine Entails.trans ?_ (BigSepL.bigSepL_perm (bufSlots_perm bufs _ hperm)).1
    rw [List.flatMap_map, BigSepL.bigSepL_flatMap]
    apply BigSepL.bigSepL_mono
    intro i e he
    unfold extB
    rw [hmem e (List.mem_of_getElem? he)]
    exact .rfl
  have e2 : ([∗list] s ∈ bufSlots bufs, slotAny (GF := GF) b p s) ⊢
      [∗list] s ∈ bufSlots bufs, ∃ a : List w8, ⌜a.length = 4096⌝ ∗
        (osSlot p s a ∗ ∃ vf, cellsR b (4096 * s) 4096 vf) := by
    apply BigSepL.bigSepL_mono
    intro i s _
    unfold slotAny cAny
    exact .rfl
  refine e1.trans ?_
  iintro H
  icases persistent_entails_right (slotsAny_nodup (GF := GF) b p _) $$ H with ⟨%hnd, H⟩
  ihave H := e2 $$ H
  icases bigSepL_choose _ _ hnd $$ H with ⟨%f, H⟩
  icases bigSepL_pure_out _ (fun s => (f s).length = 4096) _ $$ H with ⟨%Hl, H⟩
  iexists f
  isplitr
  · ipureintro; exact Hl
  unfold wrSlots
  iexact H

/-- **On success**: every page's slots, each holding its chunk, are the spec's `slotsOwn`. -/
theorem done_final (b : Loc) (l : Nat) (p : GoString) (bufs : GMap w64 (List w8))
    (L : List (w64 × Loc × List w8)) (hperm : (L.map Prod.fst).Perm (bufs.toList.map Prod.fst))
    (hmem : ∀ e ∈ L, bufs !! e.1 = some e.2.2) (hnd : (bufSlots bufs).Nodup)
    (hlen : ∀ id pg, bufs !! id = some pg → pg.length = 4096 * (1 + pageOverflow pg)) :
    ([∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
        slotDone (GF := GF) b p s (pageChunk e.2.2 (s - e.1.toNat))) ⊢
      ∃ wb' : Nat → List w8, ⌜∀ s ∈ bufSlots bufs, (wb' s).length = 4096⌝ ∗
        ⌜∀ id pg, bufs !! id = some pg → ∀ j < 1 + pageOverflow pg,
          wb' (id.toNat + j) = pageChunk pg j⌝ ∗
        slotsOwn (some (b, l) : MapSt) p (bufSlots bufs) wb' := by
  let φ : Nat → List w8 → Prop := fun s a => a.length = 4096 ∧ ∃ id pg j,
    bufs !! id = some pg ∧ j < 1 + pageOverflow pg ∧ s = id.toNat + j ∧ a = pageChunk pg j
  have e1 : ([∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
      slotDone (GF := GF) b p s (pageChunk e.2.2 (s - e.1.toNat))) ⊢
      [∗list] s ∈ bufSlots bufs, ∃ a, ⌜φ s a⌝ ∗ slotDone b p s a := by
    refine Entails.trans ?_ (BigSepL.bigSepL_perm (bufSlots_perm bufs _ hperm)).1
    rw [List.flatMap_map, BigSepL.bigSepL_flatMap]
    apply BigSepL.bigSepL_mono
    intro i e he
    have hb := hmem e (List.mem_of_getElem? he)
    unfold extB
    rw [hb]
    apply BigSepL.bigSepL_mono
    intro k s hs
    have hm := List.mem_range'_1.1 (List.mem_of_getElem? hs)
    iintro H
    iexists _
    iframe H
    ipureintro
    refine ⟨pageChunk_length _ (1 + pageOverflow e.2.2) _ (hlen _ _ hb) (by omega),
      e.1, e.2.2, s - e.1.toNat, hb, by omega, by omega, rfl⟩
  refine e1.trans ((bigSepL_choose _ _ hnd).trans ?_)
  iintro ⟨%f, H⟩
  icases bigSepL_pure_out _ (fun s => φ s (f s)) _ $$ H with ⟨%Hφ, H⟩
  iexists f
  isplitr
  · ipureintro; exact fun s hs => (Hφ s hs).1
  isplitr
  · ipureintro
    intro id pg h1 j hj
    have hs : id.toNat + j ∈ bufSlots bufs := by
      unfold bufSlots
      exact List.mem_flatMap.2 ⟨(id, pg), (GMap.mem_toList _ _ _).2 h1, by simp; omega⟩
    obtain ⟨-, id2, pg2, j2, h2, hj2, he, hf⟩ := Hφ _ hs
    have hid := bufSlots_disj bufs hnd h1 h2 hj hj2 he
    subst hid
    rw [h1] at h2; cases h2
    rw [hf]; congr 1; omega
  unfold slotsOwn
  iapply BigSepL.bigSepL_mono ?_ $$ H
  intro i s _
  unfold slotDone
  exact .rfl

end res

end bbolt
end EtcdGrove
end Perennial
