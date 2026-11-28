/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__DeleteRange.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).DeleteRange`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__DeleteRange

@[expose] public section

set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto

/-- The loop invariant of `DeleteRange`: the keys in `[mn, j)` are deleted (or `mx` is the
largest word, and the loop never ends). -/
def delInv (lm0 : GMap w64 Loc) (mn mx j : w64) (lm : GMap w64 Loc) : Prop :=
  uint.nat mx = 2 ^ 64 - 1 ∨
  (uint.nat mn ≤ uint.nat j ∧ uint.nat j ≤ Max.max (uint.nat mn) (uint.nat mx + 1) ∧
   ∀ key : w64, lm !! key =
     if uint.nat mn ≤ uint.nat key ∧ uint.nat key < uint.nat j then none else lm0 !! key)

theorem delInv_init (lm0 : GMap w64 Loc) (mn mx : w64) : delInv lm0 mn mx mn lm0 := by
  right
  refine ⟨Nat.le_refl _, by omega, ?_⟩
  intro key; rw [if_neg (by omega)]

theorem delInv_step (lm0 : GMap w64 Loc) (mn mx j : w64) (lm : GMap w64 Loc)
    (h : delInv lm0 mn mx j lm) (hj : uint.nat j ≤ uint.nat mx) :
    delInv lm0 mn mx (j + W64 1) (GMap.delete j lm) := by
  rcases h with h | ⟨h1, h2, h3⟩
  · left; exact h
  by_cases hm : uint.nat mx = 2 ^ 64 - 1
  · left; exact hm
  right
  have hlt : uint.nat mx < 2 ^ 64 := mx.isLt
  have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
  rw [hj1]
  refine ⟨by omega, by omega, ?_⟩
  intro key
  by_cases hk : key = j
  · subst hk; rw [GMap.lookup_delete, if_pos (by omega)]
  · rw [GMap.lookup_delete_ne _ (Ne.symm hk), h3 key]
    have hne : uint.nat key ≠ uint.nat j := by
      intro h; apply hk; apply BitVec.eq_of_toNat_eq; simp only [uint.nat] at h; exact h
    by_cases hr : uint.nat mn ≤ uint.nat key ∧ uint.nat key < uint.nat j
    · rw [if_pos hr, if_pos (by omega)]
    · rw [if_neg hr, if_neg (by omega)]

theorem delInv_exit (lm0 : GMap w64 Loc) (mn mx j : w64) (lm : GMap w64 Loc)
    (h : delInv lm0 mn mx j lm) (hj : ¬uint.nat j ≤ uint.nat mx) (hmx : uint.nat mx < 2 ^ 64 - 1) :
    ∀ key : w64, lm !! key =
      if uint.nat mn ≤ uint.nat key ∧ uint.nat key ≤ uint.nat mx then none else lm0 !! key := by
  have hlt : uint.nat j < 2 ^ 64 := j.isLt
  rcases h with h | ⟨h1, h2, h3⟩
  · omega
  intro key
  rw [h3 key]
  by_cases hr : uint.nat mn ≤ uint.nat key ∧ uint.nat key ≤ uint.nat mx
  · rw [if_pos (by omega), if_pos hr]
  · rw [if_neg (by omega), if_neg hr]

theorem ent_take (L : RLog) (n k : Nat) (h : k ≤ n) : ent (L.take n) k = ent L k := by
  unfold ent
  split
  · rfl
  · rw [List.getElem?_take_of_lt (by omega)]

end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.InmemStore.DeleteRange.wp_proof :
    github_com.hashicorp.raft.InmemStore.DeleteRange.spec (GF := GF) (hG := hG) :=
  fun γs i mn mx => by
  wp_start as ⟨#His, %Hmn⟩
  iNamed His
  wp_auto
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  irename i => Hrcv
  irename max => Hmax
  irename min => Hmin
  generalize i_ptr = iptr at *
  generalize max_ptr = mxp at *
  generalize min_ptr = mnp at *
  wp_apply (sync.RWMutex.wp_Lock_guard (i.[InmemStore, go!"l"]) (storeInv γs i)) $$ [$Hguard]
    with ⟨Hlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  icases (storeInv_unfold γs i 1).mp $$ HP with
    ⟨%c, Hgc, Hlow, Hhigh, Hlogsf, Hlogs, Hkvf, Hkv, Hkvintf, Hkvint, Hgl, Hgk, %Hok, #Hpers⟩
  ihave HI : (∃ (j : w64) (lm : GMap w64 Loc),
      "j" ∷ j_ptr ↦ j ∗ "Hlogs" ∷ c.mlog ↦$ lm ∗ "%Hinv" ∷ ⌜delInv c.lm mn mx j lm⌝ : IProp GF)
    $$ [j Hlogs]
  · iexists mn, c.lm; iframe; ipureintro; exact delInv_init _ _ _
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_mapDelete c.mlog lm j go.uint64 (go.GoType.PointerType Log.ty)) $$ [$Hlogs]
      with Hlogs
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    exact delInv_step _ _ _ _ _ Hinv (by word)
  wp_join iprop(∃ low1 : w64, i.[InmemStore, go!"lowIndex"] ↦ low1 ∗
      mnp ↦ mn ∗ mxp ↦ mx ∗ iptr ↦ i) with [Hlow Hmin Hmax Hrcv]
    as ⟨%low1, Hlow, Hmin, Hmax, Hrcv⟩
  wp_join iprop(∃ high1 : w64, i.[InmemStore, go!"highIndex"] ↦ high1 ∗
      mnp ↦ mn ∗ mxp ↦ mx ∗ iptr ↦ i) with [Hhigh Hmin Hmax Hrcv]
    as ⟨%high1, Hhigh, Hmin, Hmax, Hrcv⟩
  wp_join iprop(∃ low2 high2 : w64, i.[InmemStore, go!"lowIndex"] ↦ low2 ∗
      i.[InmemStore, go!"highIndex"] ↦ high2 ∗ iptr ↦ i) with [Hlow Hhigh Hrcv]
    as ⟨%low2, %high2, Hlow, Hhigh, Hrcv⟩
  -- the linearization point
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤) (E2 := ⊤ \ ↑storeN) (by solve_ndisj)) with Hmask
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%L, HL, Hclose⟩
  ihave %HLeq := inmemLogs_agree γs _ L c.L $$ HL Hgl
  subst HLeq
  have hmap := delInv_exit c.lm mn mx j lm Hinv (by word) Hmn
  let L' : LogAbs := c.L.delete (uint.nat mn) (uint.nat mx) high2
  have hdel : ∀ k, L'.m.lookup k =
      if uint.nat mn ≤ k ∧ k ≤ uint.nat mx then none else c.L.m.lookup k := by
    intro k
    show (GMap.filter _ c.L.m) !! k = _
    rw [GMap.lookup_filter]
    by_cases hr : uint.nat mn ≤ k ∧ k ≤ uint.nat mx
    · rw [if_pos hr]; cases c.L.m !! k <;> simp [Option.filter, hr]
    · rw [if_neg hr]; cases hc : c.L.m !! k <;> simp [Option.filter, hr]
  imod inmemLogs_update γs c.L c.L L' $$ HL Hgl with ⟨HL, Hgl⟩
  imod conc_update γs c { c with L := L', lo := low2, lm := lm } $$ Hgc with Hgc
  imod Hclose $$ HL with HΦ
  imod Hmask with -
  imodintro
  iframe Hnc
  ihave #Hpers' : (concPers (GF := GF) { c with L := L', lo := low2, lm := lm })
    $$ [Hpers]
  · unfold concPers
    iNamed Hpers
    isplitl
    · imodintro
      iintro %key %q %Hq
      dsimp only at Hq ⊢
      rw [hmap key] at Hq
      by_cases hr : uint.nat mn ≤ uint.nat key ∧ uint.nat key ≤ uint.nat mx
      · rw [if_pos hr] at Hq; cases Hq
      · rw [if_neg hr] at Hq
        icases Hplogs $$ %key %q %Hq with ⟨%e, %He, Hl⟩
        iexists e
        isplit
        · ipureintro; rw [hdel, if_neg hr]; exact He
        · iexact Hl
    · iexact Hpkv
  wp_apply (sync.RWMutex.wp_Unlock_guard (i.[InmemStore, go!"l"]) (storeInv γs i))
    $$ [$Hlocked Hgc Hlow Hhigh Hlogsf Hlogs Hkvf Hkv Hkvintf Hkvint Hgl Hgk]
  · inext
    iapply (storeInv_unfold γs i 1).mpr
    iexists { c with L := L', lo := low2, lm := lm }
    dsimp only
    iframe
    iframe #
    ipureintro
    refine ⟨?_, ?_, Hok.2.2⟩
    · intro k hk
      rw [hdel] at hk
      by_cases hr : uint.nat mn ≤ k ∧ k ≤ uint.nat mx
      · rw [if_pos hr] at hk; cases hk
      · rw [if_neg hr] at hk; exact Hok.1 k hk
    · intro key
      dsimp only
      rw [hmap key, hdel]
      by_cases hr : uint.nat mn ≤ uint.nat key ∧ uint.nat key ≤ uint.nat mx
      · rw [if_pos hr, if_pos hr]; exact Iff.rfl
      · rw [if_neg hr, if_neg hr, Hok.2.1 key]
  iapply HΦ


end proof

end Perennial
