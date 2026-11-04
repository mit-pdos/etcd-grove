/-
`Tx.rollback`'s synced `Reload` branch (U10f of `notes/bbolt-proof-plan.md`): the freelist page's
id (`db.meta().Freelist()`, `wp_meta_Freelist`), its extent's cells out of `wCells` and read
against the page-cache bytes `wBytes` (`ext_agree`, by `cellsR_agree_bytes` slot by slot), back
(`ext_cells_back`); `Reload`'s premises from `flCurOK` (`reload_premises`), the store's
(`reload_store_ids`) and `wdbOK` after it (`wdbOK_reload_synced`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackFacts
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.go_etcd_io.bbolt.Mmap.RemapBase
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
set_option linter.unusedSectionVars false
variable [GooseExts]

/-- A list without repeats whose members are all in `W` is, with the rest, a permutation of `W`. -/
theorem perm_append_of_nodup_sub {A : Type} [DecidableEq A] (ws W : List A) (hn : ws.Nodup)
    (hsub : ∀ s ∈ ws, s ∈ W) : ∃ rest, W.Perm (ws ++ rest) := by
  obtain ⟨l, hl, hsl⟩ := List.subperm_of_subset hn hsub
  obtain ⟨r, hr⟩ := hsl.exists_perm_append
  exact ⟨r, hr.trans (hl.append_right r)⟩

/-- A committed-pending id is a pending id. -/
theorem committedPending_mem (fl : FLPg) (C : CommitSt) (x : w64) (h : committedPending fl C x) :
    x ∈ fl.pendingIds := by
  obtain ⟨t, pd, ht, hx, -⟩ := h
  unfold FLPg.pendingIds
  exact List.mem_flatMap.2 ⟨(t, pd), (GMap.mem_toList _ _ _).2 ht, hx⟩

theorem toNat_mem_pendSlots (fl : FLPg) (x : w64) (h : x ∈ fl.pendingIds) :
    x.toNat ∈ pendSlots fl :=
  List.mem_map_of_mem h

theorem mem_pendSlots_iff (fl : FLPg) (x : w64) : x.toNat ∈ pendSlots fl ↔ x ∈ fl.pendingIds := by
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := List.mem_map.1 h
    rw [BitVec.eq_of_toNat_eq e] at hy; exact hy
  · exact toNat_mem_pendSlots fl x

/-- Distinct ids in `[2, n)` number at most `n - 2`. -/
theorem length_le_of_nodup_two (l : List w64) (n : Nat) (h2 : 2 ≤ n) (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, 2 ≤ x.toNat ∧ x.toNat < n) : l.length + 2 ≤ n := by
  have h := length_le_of_nodup_lt (W64 0 :: W64 1 :: l) n ?_ ?_
  · simp only [List.length_cons] at h; omega
  · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hnd⟩⟩
    · intro hm
      rcases List.mem_cons.1 hm with e | hm
      · exact absurd e (by decide)
      · have := (hlt _ hm).1; simp at this
    · intro hm; have := (hlt _ hm).1; simp at this
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp; omega
    rcases List.mem_cons.1 hx with rfl | hx
    · simp; omega
    · exact (hlt x hx).2

/-- **The writer side's facts about the synced freelist page's ids** (`flCurOK` and `wdbOK`): each
is at least 2, below the high-water mark, and no store slot unless pending. -/
theorem flIds_facts (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    ∀ x ∈ flIds (extentBytes w.wb f), 2 ≤ x.toNat ∧ x.toNat < w.C.hwm ∧
      (x ∈ w.fl.pendingIds ∨ (x ∉ w.fl.pendingIds ∧ ¬ coversSlot w.C.pages x.toNat)) := by
  intro x hx
  obtain ⟨-, -, -, -, -, a6, -, -, -, -, a11, -⟩ := hok
  obtain ⟨-, -, -, -, -, -, b7, -, -, -, -, b12⟩ := a6 f hf f hf
  refine ⟨b7 x hx, ?_, ?_⟩
  · rcases b12 x hx with h | h
    · exact a11 _ (.inr (toNat_mem_pendSlots _ _ (committedPending_mem _ _ _ h)))
    · exact h.1
  · by_cases hp : x ∈ w.fl.pendingIds
    · exact .inl hp
    · rcases b12 x hx with h | h
      · exact absurd (committedPending_mem _ _ _ h) hp
      · exact .inr ⟨hp, h.2.2⟩

/-- The extent's overflow is its first slot's (the header lies in it, `wb_header`). -/
theorem extent_overflow (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    pageOverflow (extentBytes w.wb f) = pageOverflow (w.wb f) := by
  have h16 := wb_header w hok f hf
  unfold pageOverflow pageHdr bytesAt
  congr 3
  unfold extentBytes
  rw [show 1 + pageOverflow (w.wb f) = (pageOverflow (w.wb f)) + 1 by omega, List.range'_succ,
    List.flatMap_cons, List.drop_zero, List.drop_zero,
    List.take_append_of_le_length h16]

/-- **`Reload`'s premises** for the synced freelist page, from `wdbOK` (`flCurOK`). -/
theorem reload_premises (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f)
    (hh : w.C.hwm ≤ 2 ^ 62) (hwf : w.fl.WF) :
    let pg := extentBytes w.wb f
    pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flCountIdx pg).1 < 2 ^ 63 ∧ (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat) ∧
    (flIds pg).length + w.fl.pendingIds.length < 2 ^ 63 ∧ (flIds pg ≠ [] ∨ w.fl.free = []) ∧
    f + (1 + pageOverflow (w.wb f)) ≤ w.C.hwm := by
  intro pg
  have hids := flIds_facts w f hok hf
  have hov : pageOverflow pg = pageOverflow (w.wb f) := extent_overflow w f hok hf
  obtain ⟨-, -, -, -, -, a6, -, -, -, -, a11, -⟩ := hok
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, -, -, b10, -, -⟩ := a6 f hf f hf
  have hlen : (flIds pg).length = (flCountIdx pg).1 := by
    simp [flIds]
  have h1 := length_le_of_nodup_two (flIds pg) w.C.hwm (by omega) b6 fun x hx => ⟨(hids x hx).1, (hids x hx).2.1⟩
  have hpnd : w.fl.pendingIds.Nodup := (List.nodup_append.1 hwf.1).2.1
  have h2 := length_le_of_nodup_lt w.fl.pendingIds w.C.hwm hpnd fun x hx =>
    a11 _ (.inr (toNat_mem_pendSlots _ _ hx))
  refine ⟨b4, b5, by omega, b6, b7, by omega, ?_, by rw [← hov]; exact b2⟩
  rcases hfr : w.fl.free with _ | ⟨x, xs⟩
  · exact .inr rfl
  · left; intro he
    have := b10 x (by rw [hfr]; exact List.mem_cons_self ..)
    rw [he] at this; exact absurd this (List.not_mem_nil)

/-- **`store_reload`'s premises** for the synced freelist page's ids. -/
theorem reload_store_ids (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f)
    (hh : w.C.hwm ≤ 2 ^ 62) :
    ∀ x ∈ flIds (extentBytes w.wb f), 2 ≤ x.toNat ∧ x.toNat < w.C.hwm ∧ x.toNat < 2 ^ 62 ∧
      (x.toNat ∉ slotsOf w.C w.fl ∨ x ∈ w.fl.pendingIds) := by
  intro x hx
  obtain ⟨a, b, c⟩ := flIds_facts w f hok hf x hx
  refine ⟨a, b, by omega, ?_⟩
  rcases c with c | ⟨c1, c2⟩
  · exact .inr c
  · left
    rw [mem_slotsOf]
    rintro (h | h)
    · exact c2 ((mem_pagesSlots_iff _ _).1 h)
    · exact c1 ((mem_pendSlots_iff _ _).1 h)

/-- **The writer side after `Reload` of the synced freelist page.** -/
theorem wdbOK_reload_synced (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    wdbOK { w with fl := w.fl.reload (flIds (extentBytes w.wb f)) } := by
  have hids := flIds_facts w f hok hf
  have hfr : ∀ x ∈ (w.fl.reload (flIds (extentBytes w.wb f))).free,
      x ∈ flIds (extentBytes w.wb f) ∧ x.toNat < w.C.hwm ∧ ¬ coversSlot w.C.pages x.toNat := by
    intro x hx
    obtain ⟨h1, h2⟩ := mem_reload_free _ _ _ hx
    obtain ⟨-, b, c⟩ := hids x h1
    rcases c with c | ⟨-, c⟩
    · exact absurd c h2
    · exact ⟨h1, b, c⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hok
  refine ⟨c1, c2, c3, c4, ?_, ?_, c7, c8, c9, c10, c11, ?_, c13, c14, c15⟩
  · intro x hx ht
    exact (hfr x hx).2.2 ((mem_pagesSlots_iff _ _).1 ht)
  · intro f' hf'
    simp only at hf' ⊢
    rw [hf] at hf'; cases hf'
    intro g hg
    rw [hf] at hg; cases hg
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := c6 f hf f hf
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun s h1 h2 => ⟨(a9 s h1 h2).1, fun hm => ?_⟩,
      fun x hx => (hfr x hx).1, a11, a12⟩
    rcases List.mem_append.1 hm with hm | hm
    · have hx := (hfr _ hm).1
      have hlt : s < 2 ^ 64 := by
        have := c11; have := (a9 s h1 h2); omega
      apply a8 _ hx
      rw [toNat_W64_of_lt _ (by omega)]
      exact ⟨h1, h2⟩
    · exact (a9 s h1 h2).2 (List.mem_append_right _ hm)
  · intro x hx; exact (hfr x hx).2.1

/-- **The synced freelist page's extent is `W` slots inside the file and the mapping**, each a
page's bytes. -/
theorem ext_in_W (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    ∀ s ∈ List.range' f (1 + pageOverflow (w.wb f)), s ∈ w.W ∧ 4096 * (s + 1) ≤ w.m.size ∧
      (∀ b l, w.ms = some (b, l) → 4096 * (s + 1) ≤ l) ∧ (w.wb s).length = 4096 := by
  intro s hs
  rw [List.mem_range'_1] at hs
  have hov := extent_overflow w f hok hf
  have c15 := hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, c3, c4, -, c6, -, c8, c9, -, -, -⟩ := hok
  obtain ⟨a1, a2, -, -, -, -, -, -, a9, -⟩ := c6 f hf f hf
  rw [hov] at a2 a9
  obtain ⟨hcov, hall⟩ := a9 s hs.1 hs.2
  have hsz : 4096 * (s + 1) ≤ w.m.size := by
    have : (s + 1) * 4096 ≤ w.C.hwm * 4096 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hW : s ∈ w.W := by
    refine (c4 s).2 ⟨by omega, ?_, fun h => hcov ((mem_pagesSlots_iff _ _).1 h), fun h => ?_⟩
    · have hM : w.m.size ≤ max (mapLen w.ms) w.m.size := Nat.le_max_right _ _
      generalize max (mapLen w.ms) w.m.size = M at hM ⊢
      omega
    · apply hall
      have hs64 : s < 2 ^ 64 := by omega
      obtain ⟨y, hy, e⟩ := List.mem_map.1 h
      have : y = W64 (s : Int) := BitVec.eq_of_toNat_eq (by rw [e, toNat_W64_of_lt _ hs64])
      rw [← this]
      exact List.mem_append_right _ hy
  refine ⟨hW, hsz, fun b l hbl => ?_, c15 s hW hsz⟩
  have := c9 b l hbl
  have : (s + 1) * 4096 ≤ w.C.hwm * 4096 := Nat.mul_le_mul_right _ (by omega)
  omega

end pure

section iris
set_option linter.unusedSectionVars false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The members of a list without repeats out of a big separating conjunction over a list holding
them**, and back. -/
theorem bigSepL_extract {A : Type} [DecidableEq A] (Φ : A → IProp GF) (ws W : List A)
    (hn : ws.Nodup) (hsub : ∀ s ∈ ws, s ∈ W) :
    ([∗list] s ∈ W, Φ s) ⊢ ([∗list] s ∈ ws, Φ s) ∗ (([∗list] s ∈ ws, Φ s) -∗ [∗list] s ∈ W, Φ s) := by
  obtain ⟨r, hr⟩ := perm_append_of_nodup_sub ws W hn hsub
  refine (BigSepL.bigSepL_perm hr).1.trans ?_
  refine BigSepL.bigSepL_append.1.trans ?_
  iintro ⟨Hw, Hr⟩
  iframe Hw
  iintro Hw
  iapply (BigSepL.bigSepL_perm hr).2
  iapply BigSepL.bigSepL_append.2
  iframe

/-- The extent's slots' cells out of `wCells`, and back. -/
theorem wCells_ext (b : Loc) (l : Nat) (W ws : List Nat) (hn : ws.Nodup) (hsub : ∀ s ∈ ws, s ∈ W)
    (hl : ∀ s ∈ ws, 4096 * (s + 1) ≤ l) :
    wCells (GF := GF) (some (b, l)) W ⊢
      ([∗list] s ∈ ws, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) ∗
      (([∗list] s ∈ ws, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) -∗
        wCells (GF := GF) (some (b, l)) W) := by
  simp only [wCells]
  iintro ⟨Hw, Hp⟩
  icases bigSepL_extract _ ws W hn hsub $$ Hw with ⟨Hws, Hback⟩
  have hc : ∀ s ∈ ws, (if 4096 * (s + 1) ≤ l then
      iprop(∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) else iprop(emp)) ⊣⊢
      iprop(∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) := by
    intro s hs; simp only [hl s hs, ↓reduceIte]; exact .rfl
  ihave Hws := bigSepL_mono_mem' (fun s hs => (hc s hs).1) $$ Hws
  iframe Hws
  iintro Hws
  ihave Hws := bigSepL_mono_mem' (fun s hs => (hc s hs).2) $$ Hws
  iframe Hp
  iapply Hback $$ Hws

/-- The extent's slots' page-cache bytes out of `wBytes`, and back. -/
theorem wBytes_ext (p : GoString) (W ws : List Nat) (wb : Nat → List w8) (size : Nat)
    (hn : ws.Nodup) (hsub : ∀ s ∈ ws, s ∈ W) (hl : ∀ s ∈ ws, 4096 * (s + 1) ≤ size) :
    wBytes (GF := GF) p W wb size ⊢
      ([∗list] s ∈ ws, ∃ xs : List (w8 × Bool), osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = wb s⌝) ∗
      (([∗list] s ∈ ws, ∃ xs : List (w8 × Bool), osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = wb s⌝) -∗ wBytes (GF := GF) p W wb size) := by
  unfold wBytes
  iintro Hw
  icases bigSepL_extract _ ws W hn hsub $$ Hw with ⟨Hws, Hback⟩
  have hc : ∀ s ∈ ws, (if 4096 * (s + 1) ≤ size then
    iprop(∃ xs : List (w8 × Bool), osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xs ∗
      ⌜xs.map Prod.fst = wb s⌝)
    else if 4096 * s < size then
      iprop(∃ xs : List (w8 × Bool), osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = (wb s).take (size - 4096 * s)⌝)
    else iprop(emp)) ⊣⊢
      iprop(∃ xs : List (w8 × Bool), osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = wb s⌝) := by
    intro s hs; simp only [hl s hs, ↓reduceIte]; exact .rfl
  ihave Hws := bigSepL_mono_mem' (fun s hs => (hc s hs).1) $$ Hws
  iframe Hws
  iintro Hws
  ihave Hws := bigSepL_mono_mem' (fun s hs => (hc s hs).2) $$ Hws
  iapply Hback $$ Hws

theorem ext_loc (b : Loc) (f : Nat) :
    b +ₗ ((4096 * f : Nat) : Int) +ₗ ((4096 : Nat) : Int) = b +ₗ ((4096 * (f + 1) : Nat) : Int) := by
  rw [loc_add_assoc]; congr 1

/-- **The extent's cells are its slots' bytes at a half** (the inverse of `ext_agree`'s reading). -/
theorem ext_cells_back (b : Loc) (wb : Nat → List w8) :
    ∀ (k f : Nat), (∀ s, f ≤ s → s < f + k → (wb s).length = 4096) →
      bytesPointsto (GF := GF) (b +ₗ ((4096 * f : Nat) : Int)) (DFrac.own (1 : Qp).half)
        ((List.range' f k).flatMap wb) ⊢
      [∗list] s ∈ List.range' f k, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf
  | 0, f, _ => by
    iintro -
    simp only [List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1, f, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine (bytesPointsto_app _ _ _ _).1.trans ?_
    have hl := h f (Nat.le_refl _) (by omega)
    rw [hl, ext_loc]
    iintro ⟨H0, Hr⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · ihave H0 := bytes_cellsR b (wb f) (4096 * f) $$ H0
      rw [hl]
      iexists _; iexact H0
    · iapply ext_cells_back b wb k (f + 1) (fun s h1 h2 => h s (by omega) (by omega)) $$ Hr

/-- **The extent's mapped cells hold its page-cache bytes** (`cellsR_agree_bytes` slot by slot,
around any step `e`): the cells give the extent's bytes at a half. -/
theorem ext_agree {st : Stuckness} {E : CoPset} (e : Expr) (htv : toVal e = none) (p : GoString)
    (dqm : DFrac) (m : OsMeta) (b : Loc) (len : Nat) (hb : m.maps !! b = some len)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) (wb : Nat → List w8) :
    ∀ (k f : Nat), (∀ s, f ≤ s → s < f + k → 4096 * (s + 1) ≤ len ∧ (wb s).length = 4096) →
    ⊢ osInv (GF := GF) -∗ osMeta (GF := GF) p dqm (some m) -∗
      ([∗list] s ∈ List.range' f k, ∃ xs : List (w8 × Bool),
        osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = wb s⌝) -∗
      ([∗list] s ∈ List.range' f k, ∃ vf, cellsR (GF := GF) b (4096 * s) 4096 vf) -∗
      (osMeta (GF := GF) p dqm (some m) -∗
        ([∗list] s ∈ List.range' f k, ∃ xs : List (w8 × Bool),
          osBytes (GF := GF) p (4096 * s) (DFrac.own 1) xs ∗ ⌜xs.map Prod.fst = wb s⌝) -∗
        bytesPointsto (GF := GF) (b +ₗ ((4096 * f : Nat) : Int)) (DFrac.own (1 : Qp).half)
          ((List.range' f k).flatMap wb) -∗
        WP e @ st; E {{ Φ }}) -∗
      WP e @ st; E {{ Φ }}
  | 0, f, _ => by
    iintro #Hinv Hm Hob Hc HΦ
    iapply HΦ $$ Hm Hob
    simp only [List.range'_zero, List.flatMap_nil, bytesPointsto]
    ipureintro; trivial
  | k + 1, f, h => by
    rw [List.range'_succ, List.flatMap_cons]
    obtain ⟨hlen, hl⟩ := h f (Nat.le_refl _) (by omega)
    iintro #Hinv Hm Hob Hc HΦ
    icases BigSepL.bigSepL_cons.1 $$ Hob with ⟨⟨%xs, Hxs, %Hx⟩, Hob⟩
    icases BigSepL.bigSepL_cons.1 $$ Hc with ⟨⟨%vf, Hc0⟩, Hc⟩
    have hxl : xs.length = 4096 := by
      have := congrArg List.length Hx; simp only [List.length_map] at this; omega
    ihave Hc0 : cellsR (GF := GF) b (4096 * f) xs.length vf $$ [Hc0]
    · rw [hxl]; iexact Hc0
    iapply cellsR_agree_bytes e htv p dqm m b len hb (DFrac.own 1) hE Φ xs (4096 * f) vf
      (by omega) $$ Hinv Hm Hxs Hc0
    iintro Hm Hxs Hc0
    ihave H0 : bytesPointsto (GF := GF) (b +ₗ ((4096 * f : Nat) : Int)) (DFrac.own (1 : Qp).half)
        (wb f) $$ [Hc0]
    · rw [← Hx]; iapply cellsR_bytes; simp only [List.length_map]; iexact Hc0
    iapply ext_agree e htv p dqm m b len hb hE Φ wb k (f + 1)
      (fun s h1 h2 => h s (by omega) (by omega)) $$ Hinv Hm Hob Hc
    iintro Hm Hob Hr
    iapply HΦ $$ Hm [Hxs Hob] [H0 Hr]
    · iapply BigSepL.bigSepL_cons.2
      iframe Hob
      iexists xs; iframe; ipureintro; exact Hx
    · iapply (bytesPointsto_app _ _ _ _).2
      rw [hl, ext_loc]
      iframe

variable [package_sem : go_etcd_io.bbolt.Assumptions] in
/-- **`db.meta().Freelist()`** of a synced freelist page `f`: its id. -/
theorem wp_meta_Freelist (wp_Freelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (b : Loc) (l : Nat) (C : CommitSt) (q : Qp) (hok : C.metaOk) (f : Nat) (hf : C.flpg = some f) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
        metaCellsQ q (some (b, l) : MapSt) C }}
      (App (Val ((b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int)) @!! go.GoType.PointerType Meta.ty
        @!! go!"Freelist")) (Val #()))
    {{ RET #(W64 (f : Int)); metaCellsQ q (some (b, l) : MapSt) C }} := by
  iintro %Φ ⟨#Hpkc, Hmc⟩ HΦ
  obtain ⟨hl0, hl1, -, -, -, -, ⟨-, -, -, hfl⟩, -⟩ := hok
  have hfl' : ∀ v : Meta, metaFlpg v = C.flpg → v.freelist' = W64 (f : Int) := by
    intro v hv
    rw [hf] at hv
    unfold metaFlpg at hv
    split at hv
    · cases hv
    · cases hv; apply BitVec.eq_of_toNat_eq; simp
  simp only [metaCellsQ]
  icases Hmc with ⟨H0, H1⟩
  rcases Nat.mod_two_eq_zero_or_one C.txid with hT | hT
  · unfold CommitSt.slot at hfl
    simp only [hT, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = ((16 : Nat) : Int) by simp [hT]]
    ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
    icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ rfl (by omega) Hp0
      $$ H0 with ⟨M0, C0⟩
    rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl]
    rw [← hfl' _ hfl]
    generalize metaOf C.m0 = v0
    wp_apply wp_Freelist _ v0 (DFrac.own q) $$ [M0] as M0
    · iframe
    ihave H0 := C0 $$ M0
    iapply HΦ; iframe
  · unfold CommitSt.slot at hfl
    simp only [show C.txid % 2 ≠ 0 by omega, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = (4096 : Int) + ((16 : Nat) : Int) by
      simp [hT], ← loc_add_assoc]
    ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
    icases bytesPointsto_view_read (V := Meta) (b +ₗ (4096 : Int)) (DFrac.own q) C.m1 16 _ rfl
      (by omega) Hp1 $$ H1 with ⟨M1, C1⟩
    rw [show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
    rw [← hfl' _ hfl]
    generalize metaOf C.m1 = v1
    wp_apply wp_Freelist _ v1 (DFrac.own q) $$ [M1] as M1
    · iframe
    ihave H1 := C1 $$ M1
    iapply HΦ; iframe

end iris

end bbolt
end EtcdGrove
end Perennial
