/-
**`Commit`'s free of the synced freelist page, its pure part** (U10m): `tx.db.freelist.Free(txid,
tx.db.page(tx.meta.Freelist()))` on the committed synced freelist page `f` (its `n = 1 +
pageOverflow (w.wb f)` slots, `W` slots under `wdbOK`): the writer side `w.freeFl f n` (the run
pending for the writer, its slots out of `W`) satisfies the flagged `wdbOK' true`, the bytes
recorded by `store_free_fl` (`fbRec`) satisfy `fbRel`, and `Free`'s and `store_free_fl`'s
premises hold, but for the page's `allocs` entry (`hal`: not the writer's txid; no clause of
`wdbOK` gives it, reported).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WdbFlag
public import Proof.go_etcd_io.bbolt.Inv.WSlots
public import Proof.go_etcd_io.bbolt.Inv.Store
import Proof.go_etcd_io.bbolt.Txn.WJoin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **The writer side after the free of the synced freelist page `f`** (`n` slots): the run
pending for the writer, its slots out of `W`. -/
def WDb.freeFl (w : WDb) (f n : Nat) : WDb :=
  { w with fl := w.fl.freePages w.wtxid (W64 (f : Int)) n, W := wMinus w.W (List.range' f n) }

proj_simps WDb.freeFl

/-- A page's overflow is read from its first 16 bytes. -/
theorem extentBytes_overflow (wb : Nat → List w8) (f : Nat) (h16 : 16 ≤ (wb f).length) :
    pageOverflow (extentBytes wb f) = pageOverflow (wb f) := by
  unfold pageOverflow pageHdr bytesAt
  congr 3
  unfold extentBytes
  rw [show 1 + pageOverflow (wb f) = (pageOverflow (wb f)) + 1 by omega, List.range'_succ,
    List.flatMap_cons, List.drop_zero, List.drop_zero,
    List.take_append_of_le_length h16]

theorem ff_W64_toNat (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s :=
  toNat_W64_of_lt s h

omit [GooseExts] in
/-- `fbRec_lookup` (`Inv/Store`'s, stated in a section with the semantics' instances). -/
theorem ff_fbRec_lookup (id : w64) (n : Nat) (pg : Nat → List w8) (s : Nat) :
    fbRec id n pg !! s = if s ∈ List.range' id.toNat n then some (pg s) else none := by
  unfold fbRec
  induction List.range' id.toNat n with
  | nil => simp
  | cons a S ih =>
    simp only [List.foldr_cons, GMap.lookup_insert_eq_iff] at ih ⊢
    by_cases h : a = s
    · subst h; simp
    · rw [if_neg h, ih]; simp [Ne.symm h]

omit [GooseExts] in
/-- The pending ids name pending slots. -/
theorem ff_pendSlots_of_mem (fl : FLPg) (x : w64) (hx : x ∈ fl.pendingIds) :
    x.toNat ∈ pendSlots fl := List.mem_map.2 ⟨x, hx, rfl⟩

/-- **The free's facts** (see the file header): the run's slots are `W` slots inside the file and
the mapping, not covered, of whole pages, below the mark; `Free`'s `canFree` (given the page's
`allocs` entry `hal` and the freelist's size `hlen`); and the flagged writer side after the free,
with the recorded bytes. -/
theorem freeFl_ok (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f)
    (hlen : w.fl.allIds.length < 2 ^ 48) :
    let n := 1 + pageOverflow (w.wb f)
    16 ≤ (w.wb f).length ∧ 2 ≤ f ∧ f + n ≤ w.C.hwm ∧ w.C.hwm < 2 ^ 51 ∧
    (∀ j < n, f + j ∈ w.W ∧ ¬ coversSlot w.C.pages (f + j) ∧ (w.wb (f + j)).length = 4096 ∧
      (∀ b l, w.ms = some (b, l) → f + j < l / 4096) ∧ 4096 * (f + j + 1) ≤ w.m.size) ∧
    ((w.fl.allocs !! W64 (f : Int)).getD 0 ≠ w.wtxid →
      w.fl.canFree w.wtxid (W64 (f : Int)) n) ∧
    wdbOK' true (w.freeFl f n) ∧ fbRel (w.freeFl f n) (fbRec (W64 (f : Int)) n w.wb) ∧
    (∀ s, f ≤ s → s < f + n → s ∈ pendSlots (w.freeFl f n).fl) := by
  intro n
  have h16 := wb_header w hok f hf
  have hov := extentBytes_overflow w.wb f h16
  obtain ⟨h1, h2, h3, h4, h5, h6, htx, hhwm, hmap, hsmall, hslots, hfree⟩ := hok
  have hlen15 := hfree.2.2.2.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := h6 f hf f hf
  rw [hov] at c2 c3 c8 c9
  have hsz : w.C.hwm * 4096 ≤ w.m.size := h3
  -- the mark below `2 ^ 48`: the slots below it are inside the mapping or the file
  have hT : w.wtxid.toNat = w.C.txid + 1 := toNat_W64_of_lt _ htx
  have hf64 : f < 2 ^ 64 := by omega
  have hfW : (W64 (f : Int)).toNat = f := toNat_W64_of_lt _ hf64
  have hn64 : (W64 (f : Int)).toNat + n < 2 ^ 64 := by rw [hfW]; omega
  have hnotAll : ∀ s, f ≤ s → s < f + n → W64 (s : Int) ∉ w.fl.allIds := fun s a b =>
    (c9 s a b).2
  have hnotPend : ∀ s, f ≤ s → s < f + n → s ∉ pendSlots w.fl := by
    intro s a b hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    apply hnotAll x.toNat a b
    have : W64 (x.toNat : Int) = x := BitVec.eq_of_toNat_eq (toNat_W64_of_lt x.toNat x.isLt)
    rw [this]
    exact List.mem_append_right _ hx
  have hnotTree : ∀ s, f ≤ s → s < f + n → s ∉ treeSlots w.C := fun s a b h =>
    (c9 s a b).1 ((mem_pagesSlots_iff _ _).1 h)
  have hinW : ∀ s, f ≤ s → s < f + n → s ∈ w.W := by
    intro s a b
    refine (h4 s).2 ⟨by omega, ?_, hnotTree s a b, hnotPend s a b⟩
    have : s < w.m.size / 4096 := by
      rw [Nat.lt_div_iff_mul_lt (by omega)]; omega
    exact Nat.lt_of_lt_of_le this (Nat.div_le_div_right (Nat.le_max_right _ _))
  have hh48 : w.C.hwm < 2 ^ 51 := by
    have := hfree.2.1; omega
  refine ⟨h16, c1, c2, hh48, fun j hj => ?_, fun hal => ?_, ?_, ?_, ?_⟩
  · -- the run's slots
    have a : f ≤ f + j := Nat.le_add_right _ _
    have b : f + j < f + n := by omega
    refine ⟨hinW _ a b, (c9 _ a b).1, hlen15 _ (hinW _ a b) (by omega), fun b' l' hb => ?_,
      by omega⟩
    have := hmap b' l' hb
    rw [Nat.lt_div_iff_mul_lt (by omega)]; omega
  · -- `canFree`
    refine ⟨by rw [hfW]; exact c1, hn64, fun x hx hm => ?_, hal, ?_⟩
    · rw [runIds_mem_toNat _ _ hn64, hfW] at hx
      have e : W64 (x.toNat : Int) = x := BitVec.eq_of_toNat_eq (toNat_W64_of_lt x.toNat x.isLt)
      exact hnotAll x.toNat hx.1 hx.2 (by rw [e]; exact hm)
    · omega
  · -- the flagged writer side
    have hpend : ∀ s, s ∈ pendSlots (w.freeFl f n).fl ↔ s ∈ pendSlots w.fl ∨ (f ≤ s ∧ s < f + n) := by
      intro s
      show s ∈ pendSlots (w.fl.freePages w.wtxid (W64 (f : Int)) n) ↔ _
      rw [pendSlots_freePages _ _ _ _ hn64, hfW]
    refine ⟨h1, h2, h3, fun s => ?_, h5, fun f' hf' => ?_, htx, hhwm, hmap, hsmall,
      fun s hs => ?_, hfree.1, hfree.2.1, hfree.2.2.1,
      fun s hs => hfree.2.2.2.1 s (List.mem_filter.1 hs).1, hfree.2.2.2.2⟩
    · show s ∈ wMinus w.W (List.range' f n) ↔ _
      simp only [wMinus, List.mem_filter, decide_eq_true_eq]
      rw [h4 s, hpend s]
      simp only [List.mem_range'_1]
      constructor
      · rintro ⟨⟨a, b, c, d⟩, e⟩
        exact ⟨a, b, c, fun h => h.elim d (fun h' => e ⟨h'.1, by omega⟩)⟩
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨a, b, c, fun h => d (.inl h)⟩, fun h => d (.inr ⟨h.1, by omega⟩)⟩
    · have hff : f' = f := by
        have : some f' = some f := hf'.symm.trans hf
        exact Option.some.inj this
      subst hff
      refine ⟨h16, fun f'' hf'' => ?_⟩
      have hff : f'' = f' := by
        have : some f'' = some f' := hf''.symm.trans hf
        exact Option.some.inj this
      subst hff
      have hcp : ∀ x, committedPending (w.fl.freePages w.wtxid (W64 (f'' : Int)) n) w.C x →
          committedPending w.fl w.C x := by
        rintro x ⟨t, pd, hp, hx, ht⟩
        rcases freePages_pending_lookup _ _ _ _ _ _ hp with ⟨-, hp'⟩ | ⟨rfl, -⟩
        · exact ⟨t, pd, hp', hx, ht⟩
        · omega
      have hcp' : ∀ x, committedPending w.fl w.C x →
          committedPending (w.fl.freePages w.wtxid (W64 (f'' : Int)) n) w.C x := by
        rintro x ⟨t, pd, hp, hx, ht⟩
        obtain ⟨pd', hp', hsub⟩ := freePages_pending_mono _ w.wtxid (W64 (f'' : Int)) n t pd hp
        exact ⟨t, pd', hp', hsub x hx, ht⟩
      simp only [WDb.freeFl.proj_wb, WDb.freeFl.proj_C, WDb.freeFl.proj_fl]
      rw [show (w.freeFl f'' n).wtxid = w.wtxid from rfl, hov]
      refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, fun s a b => ⟨(c9 s a b).1, .inr ⟨?_, ?_⟩⟩, c10,
        fun x hx => c11 x (hcp x hx), fun x hx => (c12 x hx).imp_left (hcp' x)⟩
      · exact fun hm => hnotAll s a b (List.mem_append_left _ hm)
      · intro t pd hp hm
        rcases freePages_pending_lookup _ _ _ _ _ _ hp with ⟨-, hp'⟩ | ⟨rfl, -⟩
        · exact absurd (List.mem_append_right _ (List.mem_flatMap.2
            ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp', hm⟩)) (hnotAll s a b)
        · rfl
    · show s < w.C.hwm
      rcases hs with ht | hp
      · exact hslots s (.inl ht)
      · rcases (hpend s).1 hp with hp | ⟨_, b⟩
        · exact hslots s (.inr hp)
        · omega
  · -- the recorded bytes
    intro f' hf' s a b _
    have hff : f' = f := by
      have : some f' = some f := hf'.symm.trans hf
      exact Option.some.inj this
    subst hff
    refine ⟨⟨_, GMap.lookup_insert_eq _ _ _, W64 (f' : Int), ?_, hfW⟩, ?_⟩
    · refine List.mem_append_right _ (List.mem_map.2 ⟨0, by simp; omega, ?_⟩)
      simp
    · rw [ff_fbRec_lookup, if_pos (by rw [hfW]; simp only [List.mem_range'_1]; exact ⟨a, b⟩)]
      rfl
  · intro s a b
    show s ∈ pendSlots (w.fl.freePages w.wtxid (W64 (f : Int)) n)
    rw [pendSlots_freePages _ _ _ _ hn64, hfW]
    exact .inr ⟨a, b⟩

end pure

end bbolt
end EtcdGrove
end Perennial
