/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__StoreLogs.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).StoreLogs`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__StoreLogs

@[expose] public section

set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft
open proto


/-- `LogAbs.ins` pointwise. -/
theorem LogAbs.lookup_ins (m : GMap Nat Entry) (first : Nat) (es : RLog) (k : Nat) :
    (LogAbs.ins m first es).lookup k =
      if first ≤ k ∧ k < first + es.length then es[k - first]? else m.lookup k := by
  induction es generalizing m first with
  | nil => simp only [LogAbs.ins, List.length_nil]; rw [if_neg (by omega)]
  | cons e es ih =>
    simp only [LogAbs.ins]
    rw [ih]
    show _ = _
    by_cases h1 : first + 1 ≤ k ∧ k < first + 1 + es.length
    · rw [if_pos h1, if_pos (by simp; omega)]
      rw [show k - first = (k - (first + 1)) + 1 by omega, List.getElem?_cons_succ]
    · rw [if_neg h1]
      by_cases h2 : first = k
      · subst h2
        rw [if_pos (by simp), Nat.sub_self, List.getElem?_cons_zero]
        exact (GMap.lookup_insert m first e)
      · rw [GMap.lookup_insert_ne m e h2, if_neg (by simp; omega)]

/-- The loop's invariant after `k` iterations: the first `k` pointers are inserted at
`first..first+k-1`, and `highIndex` is the larger of the old one and the last index inserted. -/
def storeLoopInv (hi0 : w64) (lm0 : GMap w64 Loc) (first : Nat) (ptrs : List Loc) (k : Nat)
    (lm : GMap w64 Loc) (high : w64) : Prop :=
  (∀ key : w64, lm !! key =
      if first ≤ uint.nat key ∧ uint.nat key < first + k then ptrs[uint.nat key - first]?
      else lm0 !! key) ∧
  (k = 0 → high = hi0) ∧
  (0 < k → high = if uint.nat hi0 < first + k - 1 then W64 (first + k - 1) else hi0)

theorem storeLoopInv_init (hi0 : w64) (lm0 : GMap w64 Loc) (first : Nat) (ptrs : List Loc) :
    storeLoopInv hi0 lm0 first ptrs 0 lm0 hi0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro key; split <;> first | omega | rfl
  · intro _; rfl
  · intro h; omega

theorem storeLoopInv_step (hi0 : w64) (lm0 : GMap w64 Loc) (first : Nat) (ptrs : List Loc)
    (k : Nat) (lm : GMap w64 Loc) (high idx : w64) (p : Loc)
    (hinv : storeLoopInv hi0 lm0 first ptrs k lm high)
    (hidx : uint.nat idx = first + k) (hp : ptrs[k]? = some p) :
    storeLoopInv hi0 lm0 first ptrs (k + 1) (<[idx := p]> lm)
      (if uint.nat high < uint.nat idx then idx else high) := by
  obtain ⟨hm, h0, hpos⟩ := hinv
  have hidxw : idx = W64 ((first + k : Nat) : Int) := by
    apply BitVec.eq_of_toNat_eq; simp only [uint.nat] at hidx; word
  refine ⟨?_, ?_, ?_⟩
  · intro key
    by_cases hk : key = idx
    · subst hk
      rw [GMap.lookup_insert]
      rw [if_pos (by omega)]
      rw [show uint.nat key - first = k by omega]; exact hp.symm
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), hm key]
      have hne : uint.nat key ≠ first + k := by
        intro h; apply hk; apply BitVec.eq_of_toNat_eq; simp only [uint.nat] at *; omega
      by_cases hr : first ≤ uint.nat key ∧ uint.nat key < first + k
      · rw [if_pos hr, if_pos (by omega)]
      · rw [if_neg hr, if_neg (by omega)]
  · intro h; omega
  · intro _
    have hlt : uint.nat idx < 2 ^ 64 := idx.isLt
    have hW : (W64 ((first : Int) + ((k + 1 : Nat) : Int) - 1)) = idx := by
      rw [hidxw]; congr 1; push_cast; omega
    rw [hW, show first + (k + 1) - 1 = first + k by omega, hidx]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [h0 hk0]
    · have hh := hpos hkpos
      by_cases hc : uint.nat hi0 < first + k - 1
      · rw [if_pos hc] at hh
        have hhn : uint.nat high = first + k - 1 := by rw [hh]; word
        rw [if_pos (by omega), if_pos (by omega)]
      · rw [if_neg hc] at hh; rw [hh]

theorem storeLoopInv_final (A : LogAbs) (es : RLog) (lm0 : GMap w64 Loc) (first : Nat)
    (ptrs : List Loc) (lm : GMap w64 Loc) (high : w64)
    (hinv : storeLoopInv A.hi lm0 first ptrs ptrs.length lm high)
    (hlen : ptrs.length = es.length) (hfl : first + es.length ≤ 2 ^ 64)
    (hok1 : ∀ k, (A.m.lookup k).isSome → k < 2 ^ 64)
    (hdom0 : ∀ key : w64, (lm0 !! key).isSome ↔ (A.m.lookup (uint.nat key)).isSome) :
    high = (A.store first es).hi ∧ (∀ k, ((A.store first es).m.lookup k).isSome → k < 2 ^ 64) ∧
    (∀ key : w64, (lm !! key).isSome ↔ ((A.store first es).m.lookup (uint.nat key)).isSome) := by
  obtain ⟨hm, h0, hpos⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · simp only [LogAbs.store]
    rcases Nat.eq_zero_or_pos ptrs.length with h00 | hp0
    · have hes : es = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [if_pos hes]; exact h0 h00
    · have hes : es ≠ [] := by intro h; rw [h, List.length_nil] at hlen; omega
      rw [if_neg hes, hpos hp0, hlen]
  · intro k hk
    simp only [LogAbs.store] at hk
    rw [LogAbs.lookup_ins] at hk
    by_cases hr : first ≤ k ∧ k < first + es.length
    · omega
    · rw [if_neg hr] at hk; exact hok1 k hk
  · intro key
    simp only [LogAbs.store]
    rw [hm key, LogAbs.lookup_ins, hlen]
    by_cases hr : first ≤ uint.nat key ∧ uint.nat key < first + es.length
    · rw [if_pos hr, if_pos hr]
      have h1 : uint.nat key - first < ptrs.length := by omega
      have h2 : uint.nat key - first < es.length := by omega
      simp [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
    · rw [if_neg hr, if_neg hr]; exact hdom0 key

end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.InmemStore.StoreLogs.wp_proof :
    github_com.hashicorp.raft.InmemStore.StoreLogs.spec (GF := GF) (hG := hG) :=
  fun γs i sl dq ptrs first es => by
  wp_start as ⟨#His, %Hlen, Hsl, #Hptrs⟩
  iNamed His
  wp_auto
  wp_apply (lc := 3) wp_with_defer as %defer Hdefer
  irename i => Hrcv
  generalize i_ptr = iptr at *
  wp_apply (sync.RWMutex.wp_Lock_guard (i.[InmemStore, go!"l"]) (storeInv γs i)) $$ [$Hguard]
    with ⟨Hlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  icases (storeInv_unfold γs i 1).mp $$ HP with ⟨%c, Hgc, Hlow, Hhigh, Hlogsf, Hlogs, Hkvf, Hkv, Hkvintf, Hkvint, Hgl, Hgk, %Hok, #Hpers⟩
  ihave HI : (∃ (k : Nat) (lm : GMap w64 Loc) (low high : w64) (lp : Loc),
      "Hctr" ∷ i_ptr ↦ W64 k ∗ "l" ∷ l_ptr ↦ lp ∗ "%Hk" ∷ ⌜k ≤ ptrs.length ∧ storeLoopInv c.L.hi c.lm first ptrs k lm high⌝ ∗
      "Hlogs" ∷ c.mlog ↦$ lm ∗
      "Hlow" ∷ i.[InmemStore, go!"lowIndex"] ↦ low ∗
      "Hhigh" ∷ i.[InmemStore, go!"highIndex"] ↦ high : IProp GF) $$ [i l Hlogs Hlow Hhigh]
  · iexists 0, c.lm, c.lo, c.L.hi, _
    iframe
    ipureintro; exact ⟨by omega, storeLoopInv_init _ _ _ _⟩
  ihave %Hsllen := ownSlice_len $$ Hsl
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hk, Hinv⟩ := Hk
    have hk : k < ptrs.length := by word
    list_elem ptrs k as p
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index sl (sint.Z (W64 k)) ptrs dq p (by word)) $$ [$Hsl] with Hsl
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hp_lookup
    icases BigSepL.bigSepL_lookup Hp_lookup $$ Hptrs with ⟨%e, %He, Hlp⟩
    unfold logPtr logIs
    icases Hlp with ⟨%lv, #Hlv, %Hidx, #Hdata⟩
    ihave Hlv2 := Hlv
    iStructNamed Hlv2
    wp_auto
    wp_apply (wp_mapInsert go.uint64 c.mlog lm lv.Index' p) $$ [$Hlogs] with Hlogs
    wp_join iprop(∃ low2 : w64, i.[InmemStore, go!"lowIndex"] ↦ low2 ∗
        l_ptr ↦ p ∗ iptr ↦ i) with [Hlow l Hrcv]
      as ⟨%low2, Hlow, l, Hrcv⟩
    wp_join iprop(∃ high2 : w64, i.[InmemStore, go!"highIndex"] ↦ high2 ∗
        ⌜high2 = if uint.nat high < uint.nat lv.Index' then lv.Index' else high⌝ ∗ l_ptr ↦ p ∗
        iptr ↦ i) with [Hhigh l Hrcv]
      as ⟨%high2, Hhigh, %Hhigh2, l, Hrcv⟩
    · iexists _; iframe; ipureintro; rw [if_pos (by word)]
    · iexists high; iframe; ipureintro; rw [if_neg (by word)]
    wp_for_post
    iframe
    iexists (k + 1), _, low2, high2, p
    have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    rw [hctr]
    iframe
    ipureintro
    refine ⟨by omega, ?_⟩
    subst Hhigh2
    exact storeLoopInv_step c.L.hi c.lm first ptrs k lm high lv.Index' p Hinv Hidx.1 Hp_lookup
  -- loop exit: all entries inserted; the linearization point
  obtain ⟨Hk, Hinv⟩ := Hk
  have hkn : k = ptrs.length := by word
  subst hkn
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤) (E2 := ⊤ \ ↑storeN) (by solve_ndisj)) with Hmask
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc2 HAU with ⟨%L, HL, Hclose⟩
  ihave %HLeq := inmemLogs_agree γs _ L c.L $$ HL Hgl
  subst HLeq
  obtain ⟨hhigh', hlen', hdom'⟩ :=
    storeLoopInv_final c.L es c.lm first ptrs lm high Hinv Hlen.1 Hlen.2 Hok.1 Hok.2.1
  subst hhigh'
  imod inmemLogs_update γs c.L c.L (c.L.store first es) $$ HL Hgl with ⟨HL, Hgl⟩
  imod conc_update γs c { c with L := c.L.store first es, lo := low, lm := lm } $$ Hgc with Hgc
  imod Hclose $$ HL with HΦ
  imod Hmask with -
  imodintro
  iframe Hnc
  ihave #Hpers' : (concPers (GF := GF) { c with L := c.L.store first es, lo := low, lm := lm }) $$ [Hpers]
  · unfold concPers
    iNamed Hpers
    isplitl
    · imodintro
      iintro %key %q %Hq
      dsimp only at Hq ⊢
      rw [Hinv.1 key] at Hq
      by_cases hr : first ≤ uint.nat key ∧ uint.nat key < first + ptrs.length
      · rw [if_pos hr] at Hq
        icases BigSepL.bigSepL_lookup Hq $$ Hptrs with ⟨%e, %He, Hl⟩
        iexists e
        isplit
        · ipureintro
          simp only [LogAbs.store]
          rw [LogAbs.lookup_ins, if_pos (by rw [← Hlen.1]; exact hr)]
          exact He
        · rw [show first + (uint.nat key - first) = uint.nat key by omega]
          iexact Hl
      · rw [if_neg hr] at Hq
        icases Hplogs $$ %key %q %Hq with ⟨%e, %He, Hl⟩
        iexists e
        isplit
        · ipureintro
          simp only [LogAbs.store]
          rw [LogAbs.lookup_ins, if_neg (by rw [← Hlen.1]; exact hr)]
          exact He
        · iexact Hl
    · iexact Hpkv
  wp_apply (sync.RWMutex.wp_Unlock_guard (i.[InmemStore, go!"l"]) (storeInv γs i))
    $$ [$Hlocked Hgc Hlow Hhigh Hlogsf Hlogs Hkvf Hkv Hkvintf Hkvint Hgl Hgk]
  · inext
    iapply (storeInv_unfold γs i 1).mpr
    iexists { c with L := c.L.store first es, lo := low, lm := lm }
    dsimp only
    iframe
    iframe #
    ipureintro
    exact ⟨hlen', hdom', Hok.2.2⟩
  iapply HΦ $$ Hsl

end proof

end Perennial
