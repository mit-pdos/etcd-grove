/-
`Bucket.spill`'s root loop's end (U9x8, `notes/bbolt-proof-plan.md`): **the root's own slots**
(`Lroot = rootOwn X0 (keys.flatMap Dc0)`, `RInv.lroot`, U9x7). A slot a position of the root
bucket covers at the start is one of them (`mem_lroot_pos`): a covered base slot, not one of a
cached child's starting tree (those are covered by the child's positions, `uTree_start_cov`, and a
slot is covered once, `covU`). Likewise a slot an unopened bucket covers (`mem_lroot_bkt`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Spill.BktSlot
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureStart

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section own
variable [GooseExts]

/-- A slot a position covers is a slot of a view page. -/
theorem coversSlot_of_pos {X : WX} {s : Nat} {bl : Loc} {pid : w64}
    (h : coverW X s (.pos bl pid)) : coversSlot X.v.pages s := by
  obtain ⟨-, -, e, he, h1, h2⟩ := h
  have aux : ∀ id : w64, (if id = W64 0 then none else
      (X.v.pages !! id.toNat).map fun pg => (id, 1 + pageOverflow pg)) = some e →
      coversSlot X.v.pages s := by
    intro id hid
    split at hid
    · cases hid
    · obtain ⟨pg, hpg, rfl⟩ := Option.map_eq_some_iff.1 hid
      exact ⟨_, pg, hpg, h1, h2⟩
  unfold WX.posExtent at he
  split at he
  · cases he
  · exact aux _ he

/-- **A slot not covered by a cached child's position is not in the children's starting
slots.** -/
theorem not_mem_Dc0 {X0 : WX} {w0 : WDb} {B0 : BRec} {keys : List GoString}
    {Dc0 : GoString → List Nat} (hpre : spillPre X0 w0.fl) (hreach : liveReach X0)
    (hfv : flViewU X0 w0.fl) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hDc0 : ∀ k c, B0.bm !! k = some c → childTodo X0 X0 w0 w0.wtxid c (Dc0 k))
    {s : Nat} {cw : CovW} (hcw : coverW X0 s cw)
    (hno : ∀ k c pid, B0.bm !! k = some c → cw ≠ .pos c pid) : s ∉ keys.flatMap Dc0 := by
  intro hm
  obtain ⟨k, hkm, hs⟩ := List.mem_flatMap.1 hm
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((hk k).1 hkm)
  obtain ⟨Cc, hCc, -, -, hne, -, -, -, hnil, hrnd⟩ := hDc0 k c hc
  by_cases hrn : Cc.bv.rootNode' = null
  · rw [(hnil hrn).1] at hs; cases hs
  · obtain ⟨rn, h, F, N, E, -, -, hu, -⟩ := hrnd hrn
    obtain ⟨pid, hpid⟩ := ((uTree_start_cov hpre hreach hfv hCc hne hu).2 s hs).2
    exact hno k c pid hc (hfv.2.1 s _ _ hcw hpid)

/-- **A slot a root position covers at the start is one of the root's own.** -/
theorem mem_rootOwn_pos {X0 : WX} {w0 : WDb} {B0 : BRec} {keys : List GoString}
    {Dc0 : GoString → List Nat} (hpre : spillPre X0 w0.fl) (hreach : liveReach X0)
    (hfv : flViewU X0 w0.fl) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hDc0 : ∀ k c, B0.bm !! k = some c → childTodo X0 X0 w0 w0.wtxid c (Dc0 k))
    {s : Nat} {pid : w64} (h : coverW X0 s (.pos X0.rl pid)) :
    s ∈ rootOwn X0 (keys.flatMap Dc0) := by
  refine mem_rootOwn.2 ⟨coversSlot_of_pos h, lCovers_of_coverW h,
    not_mem_Dc0 hpre hreach hfv hk hDc0 h fun k c pid' hc e => ?_⟩
  obtain ⟨-, -, -, -, hne, -⟩ := hDc0 k c hc
  simp only [CovW.pos.injEq] at e
  exact hne e.1.symm

/-- **A slot an unopened bucket covers at the start is one of the root's own.** -/
theorem mem_rootOwn_bkt {X0 : WX} {w0 : WDb} {B0 : BRec} {keys : List GoString}
    {Dc0 : GoString → List Nat} (hpre : spillPre X0 w0.fl) (hreach : liveReach X0)
    (hfv : flViewU X0 w0.fl) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hDc0 : ∀ k c, B0.bm !! k = some c → childTodo X0 X0 w0 w0.wtxid c (Dc0 k))
    {s : Nat} {n : GoString} (h : coverW X0 s (.bkt n)) :
    s ∈ rootOwn X0 (keys.flatMap Dc0) := by
  have hc : coversSlot X0.v.pages s := by
    obtain ⟨v, -, -, id, pg, -, hpg, h1, h2⟩ := h
    exact ⟨id, pg, hpg, h1, h2⟩
  exact mem_rootOwn.2 ⟨hc, lCovers_of_coverW h,
    not_mem_Dc0 hpre hreach hfv hk hDc0 h fun k c pid' _ e => CovW.noConfusion e⟩

/-- **Every bucket is the root or a cached child of it** (nesting depth 2: a cached child of the
root caches none, `child_bm_empty`). -/
theorem bkt_root_or_child {X : WX} (hok : wOKR X) (hreach : liveReach X) {B0 : BRec}
    (hB0 : X.t.bs !! X.rl = some B0) {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B) :
    bl = X.rl ∨ ∃ n, B0.bm !! n = some bl := by
  have hr := hreach.1 bl B hB (hok.2.2.2.2.2.1.2.2.1 bl B hB)
  clear hB B
  induction hr with
  | root => exact Or.inl rfl
  | child bl0 c B' n hB' hm _ _ =>
    by_cases hne : bl0 = X.rl
    · subst hne; rw [hB0] at hB'; cases hB'; exact Or.inr ⟨n, hm⟩
    · rw [child_bm_empty hok hB' hne, GMap.lookup_empty] at hm
      cases hm

end own

end Spill

end bbolt
end EtcdGrove
end Perennial
