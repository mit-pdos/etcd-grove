/-
The writer side after `node.free`'s `Free` (U8, `notes/bbolt-proof-plan.md`): `wdbOK` is kept when
the writer frees the extent of a page of the committed tree (its slots are tree slots, so no `W`
slot moves; the synced freelist page's slots are not covered, so its ids stay apart).

`wdbOK_free` is over `Model/Store`'s `pendSlots_freePages`, `pendingIds_freePages_perm`, and
`wdbOK`'s bounds on the writer's txid and the high-water mark.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section free
variable [GooseExts]

/-- **Freeing a page of the committed tree keeps `wdbOK`.** -/
theorem wdbOK_free (w : WDb) (id : w64) (pg : List w8) (hok : wdbOK w)
    (hpg : w.C.pages !! id.toNat = some pg)
    (hcan : w.fl.canFree w.wtxid id (1 + pageOverflow pg)) :
    wdbOK (w.withFl (w.fl.freePages w.wtxid id (1 + pageOverflow pg))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, htx, hhwm, hmap, hsmall, hslots, hfree⟩ := hok
  have hn : id.toNat + (1 + pageOverflow pg) < 2 ^ 64 := hcan.2.1
  have hS : ∀ s, id.toNat ≤ s → s < id.toNat + (1 + pageOverflow pg) → s ∈ treeSlots w.C :=
    fun s a b => (mem_pagesSlots_iff _ _).2 ⟨id.toNat, pg, hpg, a, b⟩
  have hT : w.wtxid.toNat = w.C.txid + 1 := toNat_W64_of_lt _ htx
  refine ⟨h1, h2, h3, fun s => ?_, h5, fun f hf => ?_, htx, hhwm, hmap, hsmall, fun s hs => ?_, hfree⟩
  rotate_right
  · show s < w.C.hwm
    rcases hs with ht | hp
    · exact hslots s (.inl ht)
    · rcases (pendSlots_freePages _ _ _ _ hn s).1 hp with hp | ⟨a, b⟩
      · exact hslots s (.inr hp)
      · exact hslots s (.inl (hS s a b))
  · show s ∈ w.W ↔ _
    rw [h4 s]
    show _ ↔ _ ∧ _ ∧ _ ∧ s ∉ pendSlots (w.fl.freePages w.wtxid id (1 + pageOverflow pg))
    rw [pendSlots_freePages _ _ _ _ hn]
    constructor
    · rintro ⟨a, b, c, d⟩; exact ⟨a, b, c, fun h => h.elim d (fun h' => c (hS s h'.1 h'.2))⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨a, b, c, fun h => d (Or.inl h)⟩
  · intro f' hf'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h6 f hf f' hf'
    have hcp : ∀ x, committedPending (w.fl.freePages w.wtxid id (1 + pageOverflow pg)) w.C x →
        committedPending w.fl w.C x := by
      rintro x ⟨t, pd, hp, hx, ht⟩
      rcases freePages_pending_lookup _ _ _ _ _ _ hp with ⟨-, hp'⟩ | ⟨rfl, -⟩
      · exact ⟨t, pd, hp', hx, ht⟩
      · omega
    have hcp' : ∀ x, committedPending w.fl w.C x →
        committedPending (w.fl.freePages w.wtxid id (1 + pageOverflow pg)) w.C x := by
      rintro x ⟨t, pd, hp, hx, ht⟩
      obtain ⟨pd', hp', hsub⟩ := freePages_pending_mono _ w.wtxid id _ t pd hp
      exact ⟨t, pd', hp', hsub x hx, ht⟩
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, fun s hs1 hs2 => ⟨(c9 s hs1 hs2).1, ?_⟩, c10,
      fun x hx => c11 x (hcp x hx), fun x hx => (c12 x hx).imp_left (hcp' x), fun a ha => ?_, c14⟩
    rotate_right
    · simp only [WDb.withFl, FLPg.freePages] at ha
      by_cases e : id = W64 (f' : Int)
      · rw [e, GMap.lookup_delete] at ha; cases ha
      · rw [GMap.lookup_delete_ne _ e] at ha; exact c13 a ha
    intro hm
    unfold FLPg.allIds at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact (c9 s hs1 hs2).2 (List.mem_append_left _ hm)
    · rcases List.mem_append.1 ((pendingIds_freePages_perm _ _ _ _).mem_iff.1 hm) with hm | hm
      · exact (c9 s hs1 hs2).2 (List.mem_append_right _ hm)
      · have hs64 : s < 2 ^ 64 := by simp only [WDb.withFl] at hs2; omega
        rw [runIds_mem_toNat _ _ hn, toNat_W64_of_lt _ hs64] at hm
        exact (c9 s hs1 hs2).1 ⟨id.toNat, pg, hpg, hm.1, hm.2⟩

end free

end bbolt
end EtcdGrove
end Perennial
