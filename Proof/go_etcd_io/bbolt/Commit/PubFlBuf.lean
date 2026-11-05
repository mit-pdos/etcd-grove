/-
`Commit`'s freelist page among the dirty pages (U10l of `notes/bbolt-proof-plan.md`; maintainer
12's item 4 "for U10k"): `commitFreelist`'s run, allocated from the free ids or at the mark
(`allocRes`), meets no slot of the spilled buffers (theirs are not free, by `spillBufs`, and lie
below the mark), so the records after `commitFreelist` keep `spillBufs` with the freelist page's
buffer added. `Tx.commitFreelist.spec`'s post already gives `allocRes`, so the spec needs no new
clause: this lemma derives it at the caller.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteFL
public import Spec.go_etcd_io.bbolt.Bucket__spill

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

theorem fb_W64_toNat (s : Nat) (h : s < 2 ^ 64) : (W64 (s : Int)).toNat = s := by
  simp only [W64, BitVec.toNat_ofInt]; omega

/-- The buffers and the page map after `allocRes` and `setFlPage`: the new page at `id`, the
others the input's; the mark not lower; the run's facts, from the free ids or the mark. -/
theorem allocRes_shape (X X4 : WX) (fl2 fl4 : FLPg) (txid : w64) (cnt : Nat) (p : Loc) (id : w64)
    (bs : List w8) (hal : allocRes X X4 fl2 fl4 txid cnt p id) :
    0 < cnt ∧
    (∀ k, (X4.setFlPage id bs).t.bufs !! k = if id = k then some bs else X.t.bufs !! k) ∧
    (∀ k, ((X4.setFlPage id bs).t.pm !! k).isSome ↔ (id = k ∨ (X.t.pm !! k).isSome)) ∧
    ((fl4 = fl2.alloc txid id cnt ∧ X4.t.mv.pgid' = X.t.mv.pgid' ∧
        id.toNat + cnt ≤ 2 ^ 64 ∧ ∀ x, inRun id cnt x → x ∈ fl2.free) ∨
     (id = X.t.mv.pgid' ∧ fl4 = fl2 ∧ id.toNat + cnt < 2 ^ 62 ∧
        X4.t.mv.pgid'.toNat = id.toNat + cnt)) := by
  obtain ⟨hc, -, Xr, hr, hcase⟩ := hal
  have hXr : Xr.t.bufs = X.t.bufs ∧ Xr.t.pm = X.t.pm := by
    rcases hr with rfl | ⟨Xd, b, hd, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨hd.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.1⟩
  have hX4 : ∃ h, X4 = Xr.addPage id p cnt h := by
    rcases hcase with ⟨-, -, e⟩ | ⟨-, -, -, e⟩ <;> exact ⟨_, e⟩
  obtain ⟨h, hX4e⟩ := hX4
  refine ⟨hc, fun k => ?_, fun k => ?_, ?_⟩
  · subst hX4e
    show ((Xr.t.bufs.insert id _).insert id bs) !! k = _
    simp only [GMap.lookup_insert_eq_iff, hXr.1]
    split <;> rfl
  · subst hX4e
    show ((Xr.t.pm.insert id p) !! k).isSome ↔ _
    simp only [GMap.lookup_insert_eq_iff, hXr.2]
    split <;> simp_all
  · rcases hcase with ⟨hca, hfl, e⟩ | ⟨hid, hfl, hlt, e⟩
    · left
      refine ⟨hfl, by rw [e]; rfl, hca.1, hca.2⟩
    · right
      refine ⟨hid, hfl, hlt, ?_⟩
      rw [e]
      show (id + W64 (cnt : Int)).toNat = _
      rw [BitVec.toNat_add, fb_W64_toNat cnt (by omega)]
      omega

/-- **The allocated run's facts** (`commitFreelist`'s `allocRes`): the free ids only shrink, the
pending slots stay, the mark does not go down; the run lies in `[2, mark)` and its slots are no
tree or pending slot, no free id after, no slot of a spilled buffer. -/
theorem allocRes_run (X X4 : WX) (C : CommitSt) (fl2 fl4 : FLPg) (txid : w64) (cnt : Nat)
    (p : Loc) (id : w64)
    (hb : spillBufs X C fl2) (hal : allocRes X X4 fl2 fl4 txid cnt p id)
    (hft : ∀ x ∈ fl2.free, x.toNat ∉ treeSlots C)
    (hfp : ∀ x ∈ fl2.free, x.toNat ∉ pendSlots fl2)
    (hf2 : ∀ x ∈ fl2.free, 2 ≤ x.toNat)
    (hlt : ∀ s, s ∈ treeSlots C ∨ s ∈ pendSlots fl2 → s < X.t.mv.pgid'.toNat)
    (hflt : ∀ x ∈ fl2.free, x.toNat < X.t.mv.pgid'.toNat) (h2 : 2 ≤ X.t.mv.pgid'.toNat) :
    (∀ x ∈ fl4.free, x ∈ fl2.free) ∧ fl4.pending = fl2.pending ∧
    X.t.mv.pgid'.toNat ≤ X4.t.mv.pgid'.toNat ∧ 0 < cnt ∧
    2 ≤ id.toNat ∧ id.toNat + cnt ≤ X4.t.mv.pgid'.toNat ∧
      ∀ j < cnt, id.toNat + j ∉ treeSlots C ∧ id.toNat + j ∉ pendSlots fl2 ∧
        (∀ x ∈ fl4.free, x.toNat ≠ id.toNat + j) ∧
        ∀ id' pg', X.t.bufs !! id' = some pg' → ∀ j' < 1 + pageOverflow pg',
          id'.toNat + j' ≠ id.toNat + j := by
  obtain ⟨hpm, hbs⟩ := hb
  obtain ⟨hc, -, -, hcase⟩ := allocRes_shape X X4 fl2 fl4 txid cnt p id [] hal
  have hpd : fl4.pending = fl2.pending := by
    rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl, -⟩ <;> rfl
  have hfsub : ∀ x ∈ fl4.free, x ∈ fl2.free := by
    rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl, -⟩
    · intro x hx; exact (List.mem_filter.1 hx).1
    · intro x hx; exact hx
  have hpend : pendSlots fl4 = pendSlots fl2 := by
    rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl, -⟩ <;> rfl
  have hle : X.t.mv.pgid'.toNat ≤ X4.t.mv.pgid'.toNat := by
    rcases hcase with ⟨-, e, -⟩ | ⟨rfl, -, -, e⟩
    · exact Nat.le_of_eq (by rw [e])
    · rw [e]; omega
  -- the run's facts
  have hrun : 2 ≤ id.toNat ∧ id.toNat + cnt ≤ X4.t.mv.pgid'.toNat ∧
      ∀ j < cnt, id.toNat + j ∉ treeSlots C ∧ id.toNat + j ∉ pendSlots fl2 ∧
        (∀ x ∈ fl4.free, x.toNat ≠ id.toNat + j) ∧
        ∀ id' pg', X.t.bufs !! id' = some pg' → ∀ j' < 1 + pageOverflow pg',
          id'.toNat + j' ≠ id.toNat + j := by
    rcases hcase with ⟨hfl, e, hr64, hin⟩ | ⟨hid, hfl, hr62, e⟩
    · have hmem : ∀ j < cnt, W64 ((id.toNat + j : Nat) : Int) ∈ fl2.free ∧
          (W64 ((id.toNat + j : Nat) : Int)).toNat = id.toNat + j := by
        intro j hj
        have ht := fb_W64_toNat (id.toNat + j) (by omega)
        refine ⟨hin _ ⟨by rw [ht]; omega, by rw [ht]; omega⟩, ht⟩
      have hlast := hmem (cnt - 1) (by omega)
      have e' : X4.t.mv.pgid' = X.t.mv.pgid' := e
      refine ⟨?_, ?_, fun j hj => ?_⟩
      · have := hf2 _ (hmem 0 hc).1; rw [(hmem 0 hc).2] at this; omega
      · rw [e']; have := hflt _ hlast.1; rw [hlast.2] at this; omega
      · obtain ⟨hm, ht⟩ := hmem j hj
        refine ⟨by rw [← ht]; exact hft _ hm, by rw [← ht]; exact hfp _ hm, fun x hx => ?_,
          fun id' pg' h' j' hj' he => ?_⟩
        · rw [hfl] at hx
          have hx' := (List.mem_filter.1 hx).2
          simp only [decide_eq_true_eq, inRun, not_and, Nat.not_lt] at hx'
          intro hxe
          have := hx' (by omega)
          omega
        · have hj'' := ((hbs id' pg' h').2.2.2.2 j' hj').2.2.1 _ hm
          rw [ht] at hj''; exact hj'' he.symm
    · subst hid
      refine ⟨h2, by rw [e]; exact Nat.le_refl _, fun j hj => ⟨fun ht => ?_, fun hp => ?_, fun x hx => ?_,
        fun id' pg' h' j' hj' he => ?_⟩⟩
      · have := hlt _ (Or.inl ht); omega
      · have := hlt _ (Or.inr hp); omega
      · rw [hfl] at hx; have := hflt x hx; omega
      · have := (hbs id' pg' h').2.2.2.1; omega
  exact ⟨hfsub, hpd, hle, hc, hrun⟩

/-- **The records after `commitFreelist` keep `spillBufs`** (see the file header): the freelist
page `bs` of `cnt` pages at the allocated `id`. -/
theorem spillBufs_setFlPage (X X4 : WX) (C : CommitSt) (fl2 fl4 : FLPg) (txid : w64) (cnt : Nat)
    (p : Loc) (id : w64) (bs : List w8)
    (hb : spillBufs X C fl2) (hal : allocRes X X4 fl2 fl4 txid cnt p id)
    (hft : ∀ x ∈ fl2.free, x.toNat ∉ treeSlots C)
    (hfp : ∀ x ∈ fl2.free, x.toNat ∉ pendSlots fl2)
    (hf2 : ∀ x ∈ fl2.free, 2 ≤ x.toNat)
    (hlt : ∀ s, s ∈ treeSlots C ∨ s ∈ pendSlots fl2 → s < X.t.mv.pgid'.toNat)
    (hflt : ∀ x ∈ fl2.free, x.toNat < X.t.mv.pgid'.toNat) (h2 : 2 ≤ X.t.mv.pgid'.toNat)
    (hov : pageOverflow bs = cnt - 1) (hlen : bs.length = cnt * 4096)
    (hpid : pageId bs = id.toNat) :
    spillBufs (X4.setFlPage id bs) C fl4 := by
  obtain ⟨hpm, hbs⟩ := hb
  obtain ⟨hc, hlk, hpmk, hcase⟩ := allocRes_shape X X4 fl2 fl4 txid cnt p id bs hal
  have hcnt : 1 + pageOverflow bs = cnt := by omega
  -- the free ids after, the pending slots after, the mark after
  have hfsub : ∀ x ∈ fl4.free, x ∈ fl2.free := by
    rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl, -⟩
    · intro x hx; exact (List.mem_filter.1 hx).1
    · intro x hx; exact hx
  have hpend : pendSlots fl4 = pendSlots fl2 := by
    rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl, -⟩ <;> rfl
  have hle : X.t.mv.pgid'.toNat ≤ (X4.setFlPage id bs).t.mv.pgid'.toNat := by
    show X.t.mv.pgid'.toNat ≤ X4.t.mv.pgid'.toNat
    rcases hcase with ⟨-, e, -⟩ | ⟨rfl, -, -, e⟩
    · exact Nat.le_of_eq (by rw [e])
    · rw [e]; omega
  -- the run's facts
  have hrun : 2 ≤ id.toNat ∧ id.toNat + cnt ≤ (X4.setFlPage id bs).t.mv.pgid'.toNat ∧
      ∀ j < cnt, id.toNat + j ∉ treeSlots C ∧ id.toNat + j ∉ pendSlots fl2 ∧
        (∀ x ∈ fl4.free, x.toNat ≠ id.toNat + j) ∧
        ∀ id' pg', X.t.bufs !! id' = some pg' → ∀ j' < 1 + pageOverflow pg',
          id'.toNat + j' ≠ id.toNat + j := by
    rcases hcase with ⟨hfl, e, hr64, hin⟩ | ⟨hid, hfl, hr62, e⟩
    · have hmem : ∀ j < cnt, W64 ((id.toNat + j : Nat) : Int) ∈ fl2.free ∧
          (W64 ((id.toNat + j : Nat) : Int)).toNat = id.toNat + j := by
        intro j hj
        have ht := fb_W64_toNat (id.toNat + j) (by omega)
        refine ⟨hin _ ⟨by rw [ht]; omega, by rw [ht]; omega⟩, ht⟩
      have hlast := hmem (cnt - 1) (by omega)
      have e' : (X4.setFlPage id bs).t.mv.pgid' = X.t.mv.pgid' := e
      refine ⟨?_, ?_, fun j hj => ?_⟩
      · have := hf2 _ (hmem 0 hc).1; rw [(hmem 0 hc).2] at this; omega
      · rw [e']; have := hflt _ hlast.1; rw [hlast.2] at this; omega
      · obtain ⟨hm, ht⟩ := hmem j hj
        refine ⟨by rw [← ht]; exact hft _ hm, by rw [← ht]; exact hfp _ hm, fun x hx => ?_,
          fun id' pg' h' j' hj' he => ?_⟩
        · rw [hfl] at hx
          have hx' := (List.mem_filter.1 hx).2
          simp only [decide_eq_true_eq, inRun, not_and, Nat.not_lt] at hx'
          intro hxe
          have := hx' (by omega)
          omega
        · have hj'' := ((hbs id' pg' h').2.2.2.2 j' hj').2.2.1 _ hm
          rw [ht] at hj''; exact hj'' he.symm
    · subst hid
      have e' : (X4.setFlPage X.t.mv.pgid' bs).t.mv.pgid' = X4.t.mv.pgid' := rfl
      refine ⟨h2, by rw [e', e]; exact Nat.le_refl _, fun j hj => ⟨fun ht => ?_, fun hp => ?_, fun x hx => ?_,
        fun id' pg' h' j' hj' he => ?_⟩⟩
      · have := hlt _ (Or.inl ht); omega
      · have := hlt _ (Or.inr hp); omega
      · rw [hfl] at hx; have := hflt x hx; omega
      · have := (hbs id' pg' h').2.2.2.1; omega
  obtain ⟨hr2, hrend, hrs⟩ := hrun
  refine ⟨fun k => ?_, fun k pg hk => ?_⟩
  · by_cases e : id = k
    · rw [hlk, if_pos e]
      have := (hpmk k).2 (Or.inl e)
      simpa using this
    · rw [hlk, if_neg e, ← hpm k]
      apply Bool.eq_iff_iff.2
      rw [hpmk k]
      simp [e]
  · rw [hlk] at hk
    by_cases e : id = k
    · subst e
      simp only [if_true, Option.some.injEq] at hk
      subst hk
      rw [hcnt]
      refine ⟨hpid, by rw [hlen]; omega, hr2, hrend, fun j hj => ?_⟩
      obtain ⟨c1, c2, c3, c4⟩ := hrs j hj
      refine ⟨c1, by rw [hpend]; exact c2, c3, fun id' pg' h' j' hj' he => ?_⟩
      rw [hlk] at h'
      by_cases e' : id = id'
      · exact e'.symm
      · simp only [e', if_false] at h'
        exact absurd he.symm (c4 id' pg' h' j' hj')
    · simp only [e, if_false] at hk
      obtain ⟨h1, h2', h3, h4, h5⟩ := hbs k pg hk
      refine ⟨h1, h2', h3, by omega, fun j hj => ?_⟩
      obtain ⟨c1, c2, c3, c4⟩ := h5 j hj
      refine ⟨c1, by rw [hpend]; exact c2, fun x hx => c3 x (hfsub x hx),
        fun id' pg' h' j' hj' he => ?_⟩
      rw [hlk] at h'
      by_cases e' : id = id'
      · subst e'
        simp only [if_true, Option.some.injEq] at h'
        subst h'
        rw [hcnt] at hj'
        exact absurd he ((hrs j' hj').2.2.2 k pg hk j hj)
      · simp only [e', if_false] at h'
        exact c4 id' pg' h' j' hj' he

end pure

end bbolt
end EtcdGrove
end Perennial
