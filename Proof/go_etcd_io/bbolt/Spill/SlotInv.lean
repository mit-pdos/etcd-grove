/-
The spill's slot accounting (U9e, `notes/bbolt-proof-plan.md`): `slotInv fl hwm L` (`Spill/UTree`)
through the spill's freelist steps. An allocation from the free ids or at the high-water mark adds
its run to the owned slots; a free of an owned page's run moves it from the owned slots to the
pending ones.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Spill

section slots
variable [GooseExts]

theorem slotInv_perm {fl : FLPg} {hwm : Nat} {L L' : List Nat} (hp : L.Perm L')
    (h : slotInv fl hwm L) : slotInv fl hwm L' :=
  ⟨hp.nodup_iff.1 h.1, fun s hs => h.2.1 s (hp.symm.subset hs), h.2.2⟩

theorem slotInv_hwm {fl : FLPg} {hwm hwm' : Nat} {L : List Nat} (hle : hwm ≤ hwm')
    (h : slotInv fl hwm L) : slotInv fl hwm' L :=
  ⟨h.1, fun s hs => let ⟨a, b, c⟩ := h.2.1 s hs; ⟨by omega, b, c⟩, h.2.2.1,
    fun id hid => by have := h.2.2.2 id hid; omega⟩

theorem slotInv_sub {fl : FLPg} {hwm : Nat} {L L' : List Nat} (hs : L'.Sublist L)
    (h : slotInv fl hwm L) : slotInv fl hwm L' :=
  ⟨hs.nodup h.1, fun s hm => h.2.1 s (hs.subset hm), h.2.2⟩

theorem w64_toNat_of_lt {s : Nat} (h : s < 2 ^ 62) : (W64 (s : Int)).toNat = s := by word

theorem runIds_toNat {id : w64} {n : Nat} (hn : id.toNat + n < 2 ^ 64) {j : Nat} (hj : j < n) :
    (id + W64 (j : Int)).toNat = id.toNat + j := by word

/-- The ids of a run are its slots' ids. -/
theorem mem_runIds {id : w64} {n : Nat} (hn : id.toNat + n < 2 ^ 64) {x : w64} :
    x ∈ runIds id n ↔ id.toNat ≤ x.toNat ∧ x.toNat < id.toNat + n := by
  unfold runIds
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [runIds_toNat hn hj]; omega
  · intro ⟨h1, h2⟩
    refine ⟨x.toNat - id.toNat, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [runIds_toNat hn (by omega)]; omega

/-- **A free of an owned run** (the slots `id … id + n - 1`, owned: `L` is them and `L'`): the
run pending, `L'` still owned. -/
theorem slotInv_free {fl : FLPg} {hwm : Nat} {L' : List Nat} {txid id : w64} {n : Nat}
    (h : slotInv fl hwm (List.range' id.toNat n ++ L')) :
    slotInv (fl.freePages txid id n) hwm L' := by
  obtain ⟨hnd, hL, hnd2, hlt⟩ := h
  have hn62 : ∀ j < n, id.toNat + j < 2 ^ 62 := fun j hj =>
    (hL (id.toNat + j) (List.mem_append_left _ (List.mem_range'_1.2 ⟨by omega, by omega⟩))).2.1
  have hn : id.toNat + n < 2 ^ 64 := by
    rcases n with _ | n
    · have := id.isLt; omega
    · have := hn62 n (by omega); omega
  have hperm : (fl.freePages txid id n).allIds.Perm (fl.allIds ++ runIds id n) := by
    unfold FLPg.allIds
    rw [List.append_assoc]
    exact List.Perm.append_left _ (pendingIds_freePages_perm fl txid id n)
  -- a run id is a run slot's id
  have hrun : ∀ x ∈ runIds id n, ∃ j < n, x = W64 ((id.toNat + j : Nat) : Int) := by
    intro x hx
    obtain ⟨h1, h2⟩ := (mem_runIds hn).1 hx
    refine ⟨x.toNat - id.toNat, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [w64_toNat_of_lt (hn62 _ (by omega))]; omega
  refine ⟨(List.nodup_append.1 hnd).2.1, fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := hL s (List.mem_append_right _ hs)
    refine ⟨a, b, fun hm => ?_⟩
    rcases List.mem_append.1 (hperm.subset hm) with hm | hm
    · exact c hm
    · obtain ⟨j, hj, he⟩ := hrun _ hm
      have : s = id.toNat + j := by
        have := congrArg BitVec.toNat he
        rwa [w64_toNat_of_lt b, w64_toNat_of_lt (hn62 j hj)] at this
      subst this
      exact (List.nodup_append.1 hnd).2.2 _ (List.mem_range'_1.2 ⟨by omega, by omega⟩) _ hs rfl
  · refine hperm.symm.nodup_iff.1 (List.nodup_append.2 ⟨hnd2, ?_, ?_⟩)
    · unfold runIds
      rw [List.Nodup, List.pairwise_map]
      refine List.Pairwise.imp_of_mem (fun {a b} ha hb hne e => hne ?_) List.nodup_range
      simp only [List.mem_range] at ha hb
      have := congrArg BitVec.toNat e
      rw [runIds_toNat hn ha, runIds_toNat hn hb] at this; omega
    · intro x hx y hy hxy
      subst hxy
      obtain ⟨j, hj, rfl⟩ := hrun _ hy
      exact (hL _ (List.mem_append_left _ (List.mem_range'_1.2 ⟨by omega, by omega⟩))).2.2 hx
  · intro x hx
    rcases List.mem_append.1 (hperm.subset hx) with hm | hm
    · exact hlt x hm
    · obtain ⟨j, hj, rfl⟩ := hrun _ hm
      rw [w64_toNat_of_lt (hn62 j hj)]
      exact (hL _ (List.mem_append_left _ (List.mem_range'_1.2 ⟨by omega, by omega⟩))).1

/-- **An allocation from the free ids** (the run `id … id + n - 1` free; the freelist's ids below
the mark, below `2 ^ 62`): the run owned too. -/
theorem slotInv_alloc {fl : FLPg} {hwm : Nat} {L : List Nat} {txid id : w64} {n : Nat}
    (h : slotInv fl hwm L) (hh : hwm ≤ 2 ^ 62) (hcan : fl.canAlloc id n) :
    slotInv (fl.alloc txid id n) hwm (L ++ List.range' id.toNat n) := by
  obtain ⟨hnd, hL, hnd2, hlt⟩ := h
  have hrun : ∀ j < n, W64 ((id.toNat + j : Nat) : Int) ∈ fl.free ∧ id.toNat + j < hwm := by
    intro j hj
    have hc1 := hcan.1
    have ht : (id + W64 (j : Int)).toNat = id.toNat + j := by word
    have hf := hcan.2 (id + W64 (j : Int)) (by unfold inRun; omega)
    have hl := hlt _ (List.mem_append_left _ hf)
    rw [ht] at hl
    have e : id + W64 (j : Int) = W64 ((id.toNat + j : Nat) : Int) := by
      apply BitVec.eq_of_toNat_eq; rw [ht, w64_toNat_of_lt (by omega)]
    rw [e] at hf
    exact ⟨hf, hl⟩
  have hfa : ∀ x, x ∈ (fl.alloc txid id n).allIds → x ∈ fl.allIds ∧ ¬ inRun id n x := by
    intro x hx
    unfold FLPg.allIds FLPg.alloc FLPg.pendingIds at hx
    unfold FLPg.allIds FLPg.pendingIds
    simp only [List.mem_append, List.mem_filter, decide_eq_true_iff] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | h1
    · exact ⟨Or.inl h1, h2⟩
    · refine ⟨Or.inr h1, fun hr => ?_⟩
      exact (List.nodup_append.1 hnd2).2.2 x (hcan.2 x hr) x h1 rfl
  have hsub : (fl.alloc txid id n).allIds.Sublist fl.allIds := by
    unfold FLPg.allIds FLPg.alloc FLPg.pendingIds
    exact List.Sublist.append (List.filter_sublist) (List.Sublist.refl _)
  refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_range', ?_⟩, fun s hs => ?_, hsub.nodup hnd2,
    fun x hx => hlt x (hsub.subset hx)⟩
  · intro a ha b hb hab
    subst hab
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < n ∧ a = id.toNat + j := ⟨a - id.toNat, by have := List.mem_range'_1.1 hb; omega, by have := List.mem_range'_1.1 hb; omega⟩
    exact (hL _ ha).2.2 (List.mem_append_left _ (hrun j hj).1)
  · rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨a, b, c⟩ := hL s hs
      exact ⟨a, b, fun hm => c (hfa _ hm).1⟩
    · obtain ⟨j, hj, rfl⟩ : ∃ j, j < n ∧ s = id.toNat + j := ⟨s - id.toNat, by have := List.mem_range'_1.1 hs; omega, by have := List.mem_range'_1.1 hs; omega⟩
      obtain ⟨hf, hl⟩ := hrun j hj
      refine ⟨by simpa using hl, by simp; omega, fun hm => (hfa _ hm).2 ?_⟩
      have := hcan.1
      unfold inRun; rw [w64_toNat_of_lt (by omega)]; omega

/-- **An allocation at the high-water mark** (`id` the mark; the run below `2 ^ 62`): the run
owned too, below the new mark. -/
theorem slotInv_allocHwm {fl : FLPg} {L : List Nat} {id : w64} {n : Nat}
    (h : slotInv fl id.toNat L) (hn : id.toNat + n < 2 ^ 62) :
    slotInv fl (id.toNat + n) (L ++ List.range' id.toNat n) := by
  obtain ⟨hnd, hL, hnd2, hlt⟩ := h
  refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_range', ?_⟩, fun s hs => ?_, hnd2,
    fun x hx => by have := hlt x hx; omega⟩
  · intro a ha b hb hab
    subst hab
    have := (hL a ha).1
    have := (List.mem_range'_1.1 hb); omega
  · rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨a, b, c⟩ := hL s hs
      exact ⟨by omega, b, c⟩
    · obtain ⟨j, hj, rfl⟩ : ∃ j, j < n ∧ s = id.toNat + j := ⟨s - id.toNat, by have := List.mem_range'_1.1 hs; omega, by have := List.mem_range'_1.1 hs; omega⟩
      refine ⟨by omega, by omega, fun hm => ?_⟩
      have := hlt _ hm
      rw [w64_toNat_of_lt (by omega)] at this
      omega

end slots

end Spill

end bbolt
end EtcdGrove
end Perennial
