/-
**The flagged writer side after `Commit`'s free of the synced freelist page** (maintainer 13, for
U10m): from `wdbOK w`, the writer side with the page's run `[f, f + n)` pending for the writer and
its slots out of `W` (`Commit/FreeFlPure`'s `w.freeFl f n`, written out) satisfies `wdbOK' true`
(`wdbOK'_free_fl`: `flCurOKr`'s slot clause, every slot of the extent pending for the writer only,
holds because the free made them pending); and the page's `allocs` entry is not the writer's txid
(`flAlloc_ne_wtxid`, `Free`'s `canFree` premise, from `flCurOK`'s last clause); under `wdbOK' true`
the page's slots are pending (`wdbOK'_true_extPend`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WdbFlag
public import Proof.go_etcd_io.bbolt.Inv.WSlots
import Proof.go_etcd_io.bbolt.Txn.WJoin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **The synced freelist page's `allocs` entry is not the writer's txid** (`Free`'s `canFree`
premise at `Commit`'s free: the page was allocated at a committed txid, if known). -/
theorem flAlloc_ne_wtxid (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    (w.fl.allocs !! W64 (f : Int)).getD 0 ≠ w.wtxid := by
  have htx : w.C.txid + 1 < 2 ^ 64 := hok.2.2.2.2.2.2.1
  have hT : w.wtxid.toNat = w.C.txid + 1 := toNat_W64_of_lt _ htx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, c13, -⟩ := hok.2.2.2.2.2.1 f hf f hf
  intro e
  have := congrArg BitVec.toNat e
  rw [hT] at this
  rcases h : w.fl.allocs !! W64 (f : Int) with _ | a
  · rw [h] at this; simp at this
  · rw [h] at this
    have := c13 a h
    simp only [Option.getD_some] at *
    omega

/-- **The synced freelist page's header names its id** (`flCurOK`'s last clause, read from the
extent's first slot, which holds the header: `cm_free_fl`'s `hid`). -/
theorem wb_pageId (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    pageId (w.wb f) = f := by
  have h16 := wb_header w hok f hf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpid⟩ := hok.2.2.2.2.2.1 f hf f hf
  have e : pageId (extentBytes w.wb f) = pageId (w.wb f) := by
    unfold pageId pageHdr bytesAt
    congr 3
    unfold extentBytes
    rw [show 1 + pageOverflow (w.wb f) = (pageOverflow (w.wb f)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, List.drop_zero, List.drop_zero,
      List.take_append_of_le_length h16]
  exact e.symm.trans hpid

/-- **`wdbOK' true` after `Commit`'s free of the synced freelist page** `f` (its `n = 1 +
pageOverflow (w.wb f)` slots), from `wdbOK`: the run pending for the writer, its slots out of
`W`. The record is `Commit/FreeFlPure`'s `w.freeFl f n`. -/
theorem wdbOK'_free_fl (w : WDb) (f : Nat) (hok : wdbOK w) (hf : w.C.flpg = some f) :
    wdbOK' true { w with
      fl := w.fl.freePages w.wtxid (W64 (f : Int)) (1 + pageOverflow (w.wb f)),
      W := wMinus w.W (List.range' f (1 + pageOverflow (w.wb f))) } := by
  generalize hn : 1 + pageOverflow (w.wb f) = n
  have h16 := wb_header w hok f hf
  have hov : pageOverflow (extentBytes w.wb f) = pageOverflow (w.wb f) := by
    unfold pageOverflow pageHdr bytesAt
    congr 3
    unfold extentBytes
    rw [show 1 + pageOverflow (w.wb f) = (pageOverflow (w.wb f)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, List.drop_zero, List.drop_zero,
      List.take_append_of_le_length h16]
  obtain ⟨h1, h2, h3, h4, h5, h6, htx, hhwm, hmap, hsmall, hslots, hfree⟩ := hok
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -, c14⟩ := h6 f hf f hf
  rw [hov, hn] at c2 c3 c8 c9
  have hT : w.wtxid.toNat = w.C.txid + 1 := toNat_W64_of_lt _ htx
  have hf64 : f < 2 ^ 64 := by omega
  have hfW : (W64 (f : Int)).toNat = f := toNat_W64_of_lt _ hf64
  have hn64 : (W64 (f : Int)).toNat + n < 2 ^ 64 := by rw [hfW]; omega
  have hnotAll : ∀ s, f ≤ s → s < f + n → W64 (s : Int) ∉ w.fl.allIds := fun s a b =>
    (c9 s a b).2
  have hpend : ∀ s, s ∈ pendSlots (w.fl.freePages w.wtxid (W64 (f : Int)) n) ↔
      s ∈ pendSlots w.fl ∨ (f ≤ s ∧ s < f + n) := by
    intro s
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
  · have hff : f' = f := Option.some.inj (hf'.symm.trans hf)
    subst hff
    refine ⟨h16, fun f'' hf'' => ?_⟩
    have hff : f'' = f' := Option.some.inj (hf''.symm.trans hf)
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
    simp only
    rw [hov, hn]
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, fun s a b => ⟨(c9 s a b).1, (hpend s).2 (.inr ⟨a, b⟩),
      ?_, ?_⟩, c10, fun x hx => c11 x (hcp x hx), fun x hx => (c12 x hx).imp_left (hcp' x), ?_, c14⟩
    · exact fun hm => hnotAll s a b (List.mem_append_left _ hm)
    · intro t pd hp hm
      rcases freePages_pending_lookup _ _ _ _ _ _ hp with ⟨-, hp'⟩ | ⟨rfl, -⟩
      · exact absurd (List.mem_append_right _ (List.mem_flatMap.2
          ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp', hm⟩)) (hnotAll s a b)
      · rfl
    · intro a ha
      simp only [FLPg.freePages, GMap.lookup_delete] at ha
      cases ha
  · show s < w.C.hwm
    rcases hs with ht | hp
    · exact hslots s (.inl ht)
    · rcases (hpend s).1 hp with hp | ⟨_, b⟩
      · exact hslots s (.inr hp)
      · omega

/-- **Under `wdbOK' true` the synced freelist page's slots are pending** (`flCurOKr`'s slot
clause; `Commit/TailFPure.flExtPend_of_true` is this). -/
theorem wdbOK'_true_extPend (w : WDb) (h : wdbOK' true w) :
    ∀ f, w.C.flpg = some f → ∀ s, f ≤ s → s < f + (1 + pageOverflow (w.wb f)) →
      s ∈ pendSlots w.fl := by
  intro f hf s h1 h2
  obtain ⟨h16, hr⟩ := wdbOK'_flClause true w h f hf
  have hov : pageOverflow (extentBytes w.wb f) = pageOverflow (w.wb f) := by
    unfold pageOverflow pageHdr bytesAt
    congr 3
    unfold extentBytes
    rw [show 1 + pageOverflow (w.wb f) = (pageOverflow (w.wb f)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, List.drop_zero, List.drop_zero,
      List.take_append_of_le_length h16]
  exact ((hr f hf).2.2.2.2.2.2.2.2.1 s h1 (by rw [hov]; exact h2)).2.1

end pure

end bbolt
end EtcdGrove
end Perennial
