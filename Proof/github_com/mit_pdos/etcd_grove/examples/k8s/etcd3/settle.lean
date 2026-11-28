module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.settle
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cfgSet__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__skipTo
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.landings
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mstep
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.removeAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.advance
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedHist

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore mcfg Input Output Revs)
open k8s_dist (SettleWith skipToL foreignL mstepL_same mstepL_changed advanceL_same advanceL_new)

section pure
variable [GooseExts]

/-- What `settle` pushes for `d`'s `i`-th pending write: `d` without it (no effect), or `d` with it
landed at each of `L`'s revisions. -/
def settleSuccs (L : GCfg → Input → List Nat) (d : GCfg) (i : Nat) : List GCfg :=
  if (mstepL (pendAt d i) d.st.st).1.rv = d.st.st.rv then [⟨d.st, removeAtL d.pend i⟩]
  else (L d (pendAt d i)).map fun l =>
    ⟨(kstepL (pendAt d i) (skipToL d.st (l - 1))).1, removeAtL d.pend i⟩

theorem settleWith_trans {L : GCfg → Input → List Nat} {c d e : GCfg}
    (h1 : SettleWith L c d) (h2 : SettleWith L d e) : SettleWith L c e := by
  induction h1 with
  | refl => exact h2
  | drop i hi hrv _ ih => exact .drop i hi hrv (ih h2)
  | land i l hi hrv hl _ ih => exact .land i l hi hrv hl (ih h2)

theorem settleWith_succ {L : GCfg → Input → List Nat} {d e : GCfg} {i : Nat}
    (hi : i < d.pend.length) (he : e ∈ settleSuccs L d i) : SettleWith L d e := by
  unfold settleSuccs at he
  split at he
  · rename_i hrv
    simp only [List.mem_singleton] at he
    subst he
    exact .drop i hi hrv (.refl _)
  · rename_i hrv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
    exact .land i l hi hrv hl (.refl _)

theorem settleWith_closed {L : GCfg → Input → List Nat} (S : List GCfg)
    (hcl : ∀ d ∈ S, ∀ i < d.pend.length, ∀ e ∈ settleSuccs L d i, e ∈ S)
    {c d : GCfg} (h : SettleWith L c d) (hc : c ∈ S) : d ∈ S := by
  induction h with
  | refl => exact hc
  | drop i hi hrv _ ih =>
    exact ih (hcl _ hc i hi _ (by simp [settleSuccs, hrv]))
  | land i l hi hrv hl _ ih =>
    exact ih (hcl _ hc i hi _ (by simp only [settleSuccs, if_neg hrv]; exact List.mem_map.2 ⟨l, hl, rfl⟩))

theorem hwf_foreignL (h : HSt) (hw : HWf h) (hr : uint.nat h.st.rv + 1 < 2 ^ 64) :
    HWf (foreignL h) := by
  unfold HWf at hw ⊢
  simp only [foreignL, List.length_append, List.length_singleton, List.getLast?_append,
    List.getLast?_singleton, Option.some_or]
  refine ⟨?_, by simp⟩
  rw [hw.1]; word

theorem hwf_repeat_foreignL (n : Nat) (h : HSt) (hw : HWf h) (hr : uint.nat h.st.rv + n < 2 ^ 64) :
    HWf (Nat.repeat foreignL n h) ∧ uint.nat (Nat.repeat foreignL n h).st.rv = uint.nat h.st.rv + n := by
  induction n with
  | zero => exact ⟨hw, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    simp only [Nat.repeat]
    refine ⟨hwf_foreignL _ h1 (by omega), ?_⟩
    simp only [foreignL]
    word

theorem hwf_skipToL (h : HSt) (t : Nat) (hw : HWf h) (ht : t < 2 ^ 64) : HWf (skipToL h t) := by
  unfold skipToL
  have : uint.nat h.st.rv < 2 ^ 64 := by word
  exact (hwf_repeat_foreignL (t - uint.nat h.st.rv) h hw (by omega)).1

theorem hwf_kstepL (x : Input) (h : HSt) (hw : HWf h) (hx : isWriteL x = true)
    (hr : uint.nat h.st.rv + 1 < 2 ^ 64) : HWf (kstepL x h).1 := by
  rw [kstepL_write x h hx]
  by_cases hs : (mstepL x h.st).1.rv = h.st.rv
  · rw [mstepL_same x h.st hs, advanceL_same h h.st rfl]; exact hw
  · rw [advanceL_new h _ hs]
    have := (mstepL_changed x h.st hs).1
    unfold HWf at hw ⊢
    simp only [List.length_append, List.length_singleton, List.getLast?_append,
      List.getLast?_singleton, Option.some_or]
    refine ⟨?_, by simp⟩
    rw [this, hw.1]; word

/-- The landings' revisions: the next one, or one of `R`'s or the answer's, past it. -/
theorem landingsL_mem (R : RevsL) (g : GCfg) (rv : w64) (w : Input) (b : w64) (full : Bool)
    (x : Input) (y : Output) (hok : SettleOk R y g) (hrv : uint.nat rv + 1 < 2 ^ 63)
    (l : w64) (hl : l ∈ landingsL R rv w b full x y) :
    uint.nat l = uint.nat rv + 1 ∨
      (uint.nat rv + 1 < uint.nat l ∧ uint.nat l + g.pend.length + 1 ≤ 2 ^ 63) := by
  obtain ⟨hA, hB, hF, hY, -, -, -⟩ := hok
  have hnext : uint.nat (rv + W64 1) = uint.nat rv + 1 := by word
  have hgt : ∀ r, landOkL rv w b full x y r = true → uint.nat rv + 1 < uint.nat r := by
    intro r hr
    simp only [landOkL, Bool.and_eq_true, decide_eq_true_eq] at hr
    omega
  have hfil : ∀ (S : List w64), (∀ r ∈ S, uint.nat r + g.pend.length + 1 ≤ 2 ^ 63) →
      l ∈ S.filter (landOkL rv w b full x y) →
      uint.nat rv + 1 < uint.nat l ∧ uint.nat l + g.pend.length + 1 ≤ 2 ^ 63 := by
    intro S hS hm
    obtain ⟨hm, hk⟩ := List.mem_filter.1 hm
    exact ⟨hgt l hk, hS l hm⟩
  have hkey : ∀ r ∈ (if full then R.byKey else R.fastByKey) w.Key',
      uint.nat r + g.pend.length + 1 ≤ 2 ^ 63 := by
    intro r hr
    cases full
    · exact hF _ r (by simpa using hr)
    · exact hB _ r (by simpa using hr)
  have hanc : ∀ r ∈ (R.anchors.dropWhile fun a => decide (uint.nat a < uint.nat rv)).flatMap
      (fun a => [a, a + W64 1]), uint.nat r + g.pend.length + 1 ≤ 2 ^ 63 := by
    intro r hr
    obtain ⟨a, ha, hr⟩ := List.mem_flatMap.1 hr
    have ha' := hA a ((List.dropWhile_sublist _).subset ha)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · omega
    · have : uint.nat (a + W64 1) = uint.nat a + 1 := by word
      omega
  have hy : ∀ r ∈ [y.RV'], uint.nat r + g.pend.length + 1 ≤ 2 ^ 63 := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr; exact hY
  have h1 : l ∈ [rv + W64 1] ++ ((if full then R.byKey else R.fastByKey) w.Key').filter
      (landOkL rv w b full x y) → (uint.nat l = uint.nat rv + 1 ∨
        (uint.nat rv + 1 < uint.nat l ∧ uint.nat l + g.pend.length + 1 ≤ 2 ^ 63)) := fun hm => by
    rcases List.mem_append.1 hm with hm | hm
    · simp only [List.mem_singleton] at hm
      subst hm; exact Or.inl hnext
    · exact Or.inr (hfil _ hkey hm)
  unfold landingsL at hl
  dsimp only at hl
  cases full
  · simp only [Bool.false_eq_true, if_false] at hl h1
    split at hl
    · rcases List.mem_append.1 hl with hm | hm
      · exact h1 hm
      · exact Or.inr (hfil _ hy hm)
    · exact h1 hl
  · simp only [if_true] at hl h1
    rcases List.mem_append.1 hl with hm | hm
    · split at hm
      · rcases List.mem_append.1 hm with hm | hm
        · exact h1 hm
        · exact Or.inr (hfil _ hy hm)
      · exact h1 hm
    · exact Or.inr (hfil _ hanc hm)

/-- The landings of `GoSettle R b full x y`. -/
abbrev landF (R : RevsL) (b : w64) (full : Bool) (x : Input) (y : Output) : GCfg → Input → List Nat :=
  fun c w => (landingsL R c.st.st.rv w b full x y).map uint.nat

/-- What every configuration `settle` reaches from `g` keeps. -/
def SGood (g e : GCfg) : Prop :=
  HWf e.st ∧ (∀ p ∈ e.pend, isWriteL p = true) ∧ e.pend.length ≤ g.pend.length ∧
  e.st.st.items.length + e.pend.length ≤ g.st.st.items.length + g.pend.length ∧
  uint.nat e.st.st.rv + e.pend.length + 1 ≤ 2 ^ 63

theorem sgood_init (R : RevsL) (y : Output) (g : GCfg) (hw : HWf g.st) (hok : SettleOk R y g) :
    SGood g g :=
  ⟨hw, hok.2.2.2.2.2.2, Nat.le_refl _, Nat.le_refl _, hok.2.2.2.2.1⟩

theorem sgood_succ (R : RevsL) (b : w64) (full : Bool) (x : Input) (y : Output) (g d e : GCfg)
    (i : Nat) (hok : SettleOk R y g) (hd : SGood g d) (hi : i < d.pend.length)
    (he : e ∈ settleSuccs (landF R b full x y) d i) : SGood g e := by
  obtain ⟨hw, hp, hpl, hit, hrv⟩ := hd
  have hlen := length_removeAtL d.pend i hi
  have hpw : ∀ p ∈ removeAtL d.pend i, isWriteL p = true := fun p hp' => hp p (mem_removeAtL hp')
  have hx : isWriteL (pendAt d i) = true := by
    rw [pendAt_eq d i hi]; exact hp _ (List.getElem_mem hi)
  unfold settleSuccs at he
  split at he
  · simp only [List.mem_singleton] at he
    subst he
    refine ⟨hw, hpw, ?_, ?_, ?_⟩ <;> simp only <;> omega
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
    obtain ⟨lw, hlw, rfl⟩ := List.mem_map.1 hl
    have hm := landingsL_mem R g d.st.st.rv (pendAt d i) b full x y hok (by omega) lw hlw
    have hge : uint.nat d.st.st.rv + 1 ≤ uint.nat lw := by omega
    have hlt : uint.nat lw + d.pend.length ≤ 2 ^ 63 := by omega
    have hw' : HWf (skipToL d.st (uint.nat lw - 1)) := hwf_skipToL _ _ hw (by omega)
    have hrv' : uint.nat (skipToL d.st (uint.nat lw - 1)).st.rv = uint.nat lw - 1 := by
      rw [k8s_dist.skipToL_rv _ _ (by omega)]; omega
    have hit' : (skipToL d.st (uint.nat lw - 1)).st.items = d.st.st.items := k8s_dist.skipToL_items _ _
    have hk := kstepL_write (pendAt d i) (skipToL d.st (uint.nat lw - 1)) hx
    have hst : (kstepL (pendAt d i) (skipToL d.st (uint.nat lw - 1))).1.st =
        (mstepL (pendAt d i) (skipToL d.st (uint.nat lw - 1)).st).1 := by
      rw [hk]; exact advanceL_items _ _
    have hil := mstepL_length (pendAt d i) (skipToL d.st (uint.nat lw - 1)).st
    have hrvl : uint.nat (mstepL (pendAt d i) (skipToL d.st (uint.nat lw - 1)).st).1.rv ≤ uint.nat lw := by
      rcases mstepL_rv (pendAt d i) (skipToL d.st (uint.nat lw - 1)).st with h | h <;> rw [h]
      · omega
      · word
    refine ⟨hwf_kstepL _ _ hw' hx (by omega), hpw, ?_, ?_, ?_⟩
    · simp only; omega
    · simp only; rw [hst]; rw [hit'] at hil; omega
    · simp only; rw [hst]; omega

/-- What `settle` pushes for `d`'s first `j` pending writes. -/
def settleSuccsUpTo (L : GCfg → Input → List Nat) (d : GCfg) (j : Nat) : List GCfg :=
  (List.range j).flatMap (settleSuccs L d)

theorem settleSuccsUpTo_succ (L : GCfg → Input → List Nat) (d : GCfg) (j : Nat) :
    settleSuccsUpTo L d (j + 1) = settleSuccsUpTo L d j ++ settleSuccs L d j := by
  simp [settleSuccsUpTo, List.range_succ, List.flatMap_append]

/-- **`settle`'s worklist invariant** (§2.2): everything in the set (`sgs`) or the worklist (`wgs`) is
reached from `g` and keeps `SGood`; `g` is in one of them; the set's successors are in one of them. -/
def SetInv (L : GCfg → Input → List Nat) (g : GCfg) (sgs wgs : List GCfg) : Prop :=
  (∀ e ∈ sgs ++ wgs, SettleWith L g e ∧ SGood g e) ∧ g ∈ sgs ++ wgs ∧
  ∀ d ∈ sgs, ∀ i < d.pend.length, ∀ e ∈ settleSuccs L d i, e ∈ sgs ++ wgs

theorem setInv_init (L : GCfg → Input → List Nat) (g : GCfg) (hg : SGood g g) :
    SetInv L g [] [g] :=
  ⟨fun e he => by simp at he; subst he; exact ⟨.refl _, hg⟩, by simp, fun d hd => by simp at hd⟩

theorem setInv_skip {L : GCfg → Input → List Nat} {g d : GCfg} {sgs wg : List GCfg}
    (h : SetInv L g sgs (wg ++ [d])) (hm : d ∈ sgs) : SetInv L g sgs wg := by
  obtain ⟨h1, h2, h3⟩ := h
  have sub : ∀ e, e ∈ sgs ++ (wg ++ [d]) → e ∈ sgs ++ wg := fun e he => by
    simp only [List.mem_append, List.mem_singleton] at he ⊢
    rcases he with he | he | rfl
    · exact Or.inl he
    · exact Or.inr he
    · exact Or.inl hm
  refine ⟨fun e he => h1 e (by simp only [List.mem_append] at he ⊢; rcases he with he | he <;> simp [he]), sub _ h2,
    fun d' hd i hi e he => sub _ (h3 d' hd i hi e he)⟩

theorem setInv_add (R : RevsL) (b : w64) (full : Bool) (x : Input) (y : Output) {g d : GCfg}
    {sgs wg : List GCfg} (hok : SettleOk R y g) (h : SetInv (landF R b full x y) g sgs (wg ++ [d])) :
    SetInv (landF R b full x y) g (sgs ++ [d])
      (wg ++ settleSuccsUpTo (landF R b full x y) d d.pend.length) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := h1 d (by simp)
  have sub : ∀ e, e ∈ sgs ++ (wg ++ [d]) →
      e ∈ (sgs ++ [d]) ++ (wg ++ settleSuccsUpTo (landF R b full x y) d d.pend.length) :=
    fun e he => by
      simp only [List.mem_append, List.mem_singleton] at he ⊢
      rcases he with he | he | he <;> simp [he]
  have hsu : ∀ e ∈ settleSuccsUpTo (landF R b full x y) d d.pend.length,
      ∃ i < d.pend.length, e ∈ settleSuccs (landF R b full x y) d i := by
    intro e he
    obtain ⟨i, hi, he⟩ := List.mem_flatMap.1 he
    exact ⟨i, List.mem_range.1 hi, he⟩
  refine ⟨fun e he => ?_, sub _ h2, fun d' hd' i hi e he => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (he | rfl) | he | he
    · exact h1 e (by simp [he])
    · exact hd
    · exact h1 e (by simp [he])
    · obtain ⟨i, hi, he⟩ := hsu e he
      exact ⟨settleWith_trans hd.1 (settleWith_succ hi he), sgood_succ R b full x y g d e i hok hd.2 hi he⟩
  · simp only [List.mem_append, List.mem_singleton] at hd'
    rcases hd' with hd' | rfl
    · exact sub _ (h3 d' hd' i hi e he)
    · simp only [List.mem_append]
      exact Or.inr (Or.inr (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, he⟩))

theorem setInv_done {L : GCfg → Input → List Nat} {g : GCfg} {sgs : List GCfg}
    (h : SetInv L g sgs []) : (∀ e, e ∈ sgs ↔ SettleWith L g e) ∧ ∀ e ∈ sgs, HWf e.st := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [List.append_nil] at h1 h2 h3
  refine ⟨fun e => ⟨fun he => (h1 e he).1, fun he => settleWith_closed sgs h3 he h2⟩,
    fun e he => (h1 e he).2.1⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem settle.wp_proof
    (wp_cfgSet__add : cfgSet.add.spec (GF := GF) (hG := hG))
    (wp_mstep : mstep.spec (GF := GF) (hG := hG))
    (wp_removeAt : removeAt.spec (GF := GF) (hG := hG))
    (wp_landings : landings.spec (GF := GF) (hG := hG))
    (wp_skipTo : histHashes.skipTo.spec (GF := GF) (hG := hG))
    (wp_advance : advance.spec (GF := GF) (hG := hG)) :
    settle.spec (GF := GF) (hG := hG) := by
  intro hh r R c g b full x y
  wp_start as ⟨#Hhh, #Hr, #Hc, %Hpre⟩
  obtain ⟨Hwf, Hok⟩ := Hpre
  wp_auto
  irename hh => Hhhp
  iStructNamed set
  irename : ("_" ∷ True : IProp GF) => Hjunk
  iclear Hjunk
  ihave Hset : cfgSetOwn (GF := GF) set_ptr hh [] $$ [hh list buckets]
  · iunfold cfgSetOwn
    iexists slice.nil, map.nil, [], ∅
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
      iempintro
    isplitl
    · ipureintro; simp
    ileft
    ipureintro; exact ⟨rfl, rfl⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := mcfg) (l := [c])
  isplitr
  · ipureintro; rfl
  iintro %wsl ⟨Hw, Hwcap⟩
  wp_auto
  irename : (in_ptr ↦ x : IProp GF) => Hin
  ihave HI : (∃ (sw : GoSlice) (wcs : List mcfg) (sgs wgs : List GCfg),
      "Hset" ∷ cfgSetOwn set_ptr hh sgs ∗
      "work" ∷ work_ptr ↦ sw ∗ "Hw" ∷ sw ↦* wcs ∗
      "Hwcap" ∷ ownSliceCap mcfg sw (DFrac.own 1) ∗
      "#Hwcs" ∷ ([∗list] c;g ∈ wcs;wgs, cfgOwn c g) ∗
      "%Hinv" ∷ ⌜SetInv (landF R b full x y) g sgs wgs⌝ : IProp GF) $$ [Hset work Hw Hwcap]
  · iexists _, [c], [], [g]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_singleton.2; iexact Hc
    ipureintro; exact setInv_init _ g (sgood_init R y g Hwf Hok)
  wp_for HI
  ihave %Hwl := ownSlice_len $$ Hw
  ihave %Hwlen := BigSepL2.bigSepL2_length $$ Hwcs
  have Hw0 : ¬ 0 < sint.Z sw.len → wcs = [] := fun hz => List.eq_nil_of_length_eq_zero (by word)
  wp_if_destruct
  · have Hpos : 0 < sint.Z sw.len := by
      have h0 : sint.Z (W64 0) = 0 := rfl
      rw [h0] at Hif; exact Hif
    obtain ⟨wc, d, rfl⟩ : ∃ wc d, wcs = wc ++ [d] := by
      rcases List.eq_nil_or_concat wcs with h0 | ⟨wc, d, h0⟩
      · exfalso; subst h0; simp only [List.length_nil] at Hwl; word
      · exact ⟨wc, d, by rw [h0, List.concat_eq_append]⟩
    obtain ⟨wg, h, rfl⟩ : ∃ wg h, wgs = wg ++ [h] := by
      rcases List.eq_nil_or_concat wgs with h0 | ⟨wg, h, h0⟩
      · exfalso; subst h0; simp at Hwlen
      · exact ⟨wg, h, by rw [h0, List.concat_eq_append]⟩
    simp only [List.length_append, List.length_singleton] at Hwl Hwlen
    icases (BigSepL2.bigSepL2_snoc (Φ := fun _ c g => cfgOwn (GF := GF) c g)).1 $$ Hwcs
      with ⟨#Hwc, #Hd⟩
    ihave %Hcw := ownSliceCap_wf $$ Hwcap
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index sw (sint.Z (sw.len - W64 1)) (wc ++ [d]) _ d (by word) $$ [Hw]
      as Hw
    · iframe; ipureintro
      rw [show (sint.Z (sw.len - W64 1)).toNat = wc.length by word]; simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
    icases ownSlice_slice_with_cap (W64 0) (sw.len - W64 1) sw (wc ++ [d])
      ⟨by word, by word, by word⟩ $$ [$Hw $Hwcap] with ⟨-, Hw, Hwcap⟩
    rw [show subslice (sint.nat (W64 0)) (sint.nat (sw.len - W64 1)) (wc ++ [d]) = wc by
      rw [show sint.nat (sw.len - W64 1) = wc.length by word, show sint.nat (W64 0) = 0 from rfl]
      simp [subslice]]
    wp_auto
    wp_apply wp_cfgSet__add set_ptr hh sgs d h $$ [$Hset $Hd $Hhh] as %ok Hset
    cases ok
    case false =>
      isimp only [Bool.false_eq_true, ↓reduceIte] at Hset
      icases Hset with ⟨Hset, %hm⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists (slice.slice sw mcfg (W64 0) (sw.len - W64 1)), wc, sgs, wg
      iframe
      isplitl []
      · iexact Hwc
      ipureintro; exact setInv_skip Hinv hm
    (try wp_auto)
    have hgood : SGood g h := (Hinv.1 h (by simp)).2
    have hgw := hgood
    obtain ⟨hhw, hpw, hpl, hit, hrv⟩ := hgw
    ihave #Hd' : cfgOwn (GF := GF) d h $$ [Hd]
    · iexact Hd
    isimp only [cfgOwn] at Hd'
    icases Hd' with ⟨#Hds, #Hdh, #Hdp, %Hdhl⟩
    ihave %Hpl := ownSlice_len $$ Hdp
    isimp only [storeOwn] at Hds
    icases Hds with ⟨#Hdsi, %Hdsrv⟩
    rename_i iu_ptr
    irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
    ihave HJ : (∃ (j iv : w64) (e0 : Input) (sw' : GoSlice) (ncs : List mcfg),
        "i" ∷ i_ptr ↦ j ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "w" ∷ w_ptr ↦ e0 ∗
        "work" ∷ work_ptr ↦ sw' ∗ "Hw" ∷ sw' ↦* (wc ++ ncs) ∗
        "Hwcap" ∷ ownSliceCap mcfg sw' (DFrac.own 1) ∗
        "#Hn" ∷ ([∗list] c;g ∈ ncs;settleSuccsUpTo (landF R b full x y) h (sint.nat j), cfgOwn c g) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z d.pend'.len⌝ : IProp GF)
      $$ [i Hiu w work Hw Hwcap]
    · iexists W64 0, _, _, _, []
      rw [List.append_nil, show sint.nat (W64 0) = 0 from rfl]
      iframe
      isplitl []
      · unfold settleSuccsUpTo; simp only [List.range_zero, List.flatMap_nil]
        iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
        iempintro
      ipureintro; word
    wp_for HJ
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z d.pend'.len := ⟨Hj.1, by simpa using Hif⟩
      have hjl : sint.nat j < h.pend.length := by word
      have hits : h.st.st.items.length + 1 < 2 ^ 63 := by have := Hok.2.2.2.2.2.1; omega
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem h.pend (sint.nat j) as w
      have hx : pendAt h (sint.nat j) = w := by
        rw [pendAt_eq h _ hjl]
        exact Option.some.inj ((List.getElem?_eq_getElem hjl).symm.trans Hw_lookup)
      wp_apply wp_load_slice_index d.pend' (sint.Z j) h.pend DFrac.discard w Hj.1 $$ [Hdp] as Hjunk
      · isplit
        · iexact Hdp
        · ipureintro; exact Hw_lookup
      iclear Hjunk
      (try wp_auto)
      wp_apply wp_removeAt d.pend' h.pend DFrac.discard j $$ [$Hdp] as %np ⟨-, Hnp, -⟩
      · ipureintro; exact Hb'
      ipersist Hnp
      (try wp_auto)
      wp_apply wp_mstep w d.st' h.st.st $$ [] as %nk %o ⟨#Hnk, -⟩
      · iunfold storeOwn
        iframe #
        ipureintro; exact ⟨Hdsrv, by omega⟩
      isimp only [storeOwn] at Hnk
      icases Hnk with ⟨#Hnki, %Hnkrv⟩
      (try wp_auto)
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      wp_if_destruct
      · -- no effect: `d` without the write
        have hsame : (mstepL w h.st.st).1.rv = h.st.st.rv := by rw [← Hnkrv, ← Hdsrv]; exact Hif
        wp_apply wp_slice_literal (l := [(⟨d.st', np, d.hist'⟩ : mcfg)])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Hw $Hwcap $Hl1] as %sw'' ⟨Hw, Hwcap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _, _, sw'', ncs ++ [(⟨d.st', np, d.hist'⟩ : mcfg)]
        rw [List.append_assoc]
        iframe
        have hs : settleSuccs (landF R b full x y) h (sint.nat j) =
            [⟨h.st, removeAtL h.pend (sint.nat j)⟩] := by
          simp only [settleSuccs, hx, if_pos hsame]
        rw [hj1, settleSuccsUpTo_succ, hs]
        isplitl []
        · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ c g => cfgOwn (GF := GF) c g)).2
          isplit
          · iexact Hn
          · iunfold cfgOwn
            isplitr
            · iunfold storeOwn
              isplitr
              · iexact Hdsi
              · ipureintro; exact Hdsrv
            isplitr
            · iexact Hdh
            isplitr
            · iexact Hnp
            · ipureintro; exact Hdhl
        ipureintro; word
      · have hdiff : (mstepL w h.st.st).1.rv ≠ h.st.st.rv := by
          intro he; apply Hif; rw [Hnkrv, Hdsrv, he]
        have hwr : isWriteL w = true := hpw w (List.mem_of_getElem? Hw_lookup)
        wp_apply wp_landings r R d w b full x y $$ [$Hr] as %lsl ⟨Hls, -⟩
        rw [Hdsrv]
        imod ownSlice_persist _ _ _ $$ Hls with #Hls
        ihave %Hlsl := ownSlice_len $$ Hls
        (try wp_auto)
        let land : w64 → GCfg := fun lw =>
          ⟨(kstepL w (skipToL h.st (uint.nat lw - 1))).1, removeAtL h.pend (sint.nat j)⟩
        ihave HK : (∃ (k : w64) (lv : w64) (sw'' : GoSlice) (ncs' : List mcfg),
            "Hk" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗
            "work" ∷ work_ptr ↦ sw'' ∗ "Hw" ∷ sw'' ↦* (wc ++ ncs ++ ncs') ∗
            "Hwcap" ∷ ownSliceCap mcfg sw'' (DFrac.own 1) ∗
            "#Hn'" ∷ ([∗list] c;g ∈ ncs';((landingsL R h.st.st.rv w b full x y).take (sint.nat k)).map land,
              cfgOwn c g) ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z lsl.len⌝ : IProp GF) $$ [i l work Hw Hwcap]
        · iexists W64 0, _, _, []
          rw [List.append_nil, show sint.nat (W64 0) = 0 from rfl]
          iframe
          isplitl []
          · simp only [List.take_zero, List.map_nil]
            iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
            iempintro
          ipureintro; word
        wp_for HK
        wp_if_destruct
        · have Hkb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z lsl.len := ⟨Hk.1, Hif⟩
          simp only [Hkb, _root_.and_self, ↓reduceIte]
          list_elem (landingsL R h.st.st.rv w b full x y) (sint.nat k) as lw
          wp_apply wp_load_slice_index lsl (sint.Z k) _ DFrac.discard lw Hk.1 $$ [Hls] as Hjunk
          · isplit
            · iexact Hls
            · ipureintro; exact Hlw_lookup
          iclear Hjunk
          have hlm := landingsL_mem R g h.st.st.rv w b full x y Hok (by omega) lw
            (List.mem_of_getElem? Hlw_lookup)
          have hlw1 : uint.nat (lw - W64 1) = uint.nat lw - 1 := by word
          (try wp_auto)
          wp_apply wp_skipTo hh d h (lw - W64 1) $$ [] as %e #He
          · iframe #
            ipureintro; exact ⟨hhw, by rw [hlw1]; omega⟩
          rw [hlw1]
          ihave #He' : cfgOwn (GF := GF) e ⟨skipToL h.st (uint.nat lw - 1), h.pend⟩ $$ [He]
          · iexact He
          isimp only [cfgOwn] at He'
          icases He' with ⟨#Hes, #Heh, #Hep, %Hehl⟩
          have hsw : HWf (skipToL h.st (uint.nat lw - 1)) := hwf_skipToL _ _ hhw (by omega)
          have hsi : (skipToL h.st (uint.nat lw - 1)).st.items = h.st.st.items :=
            k8s_dist.skipToL_items _ _
          have hsr : uint.nat (skipToL h.st (uint.nat lw - 1)).st.rv = uint.nat lw - 1 := by
            rw [k8s_dist.skipToL_rv _ _ (by omega)]; omega
          (try wp_auto)
          wp_apply wp_mstep w e.st' (skipToL h.st (uint.nat lw - 1)).st $$ [$Hes] as %nk2 %o2 ⟨#Hnk2, -⟩
          · ipureintro; rw [hsi]; omega
          (try wp_auto)
          wp_apply wp_advance e ⟨skipToL h.st (uint.nat lw - 1), h.pend⟩ nk2
            (mstepL w (skipToL h.st (uint.nat lw - 1)).st).1 np (removeAtL h.pend (sint.nat j))
            $$ [$He $Hnk2 $Hnp] as %c' #Hc'
          · ipureintro; simp only; rw [hsw.1]; omega
          have hland : (⟨advanceL (skipToL h.st (uint.nat lw - 1))
              (mstepL w (skipToL h.st (uint.nat lw - 1)).st).1, removeAtL h.pend (sint.nat j)⟩ : GCfg) =
              land lw := by
            simp only [land, kstepL_write w _ hwr]
          rw [hland]
          wp_apply wp_slice_literal (l := [c'])
          isplitr
          · ipureintro; rfl
          iintro %lsl1 ⟨Hl1, _⟩
          wp_apply wp_slice_append $$ [$Hw $Hwcap $Hl1] as %sw3 ⟨Hw, Hwcap, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists k + W64 1, lw, sw3, ncs' ++ [c']
          rw [List.append_assoc, List.append_assoc]
          iframe
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          rw [hk1, List.take_add_one, Hlw_lookup, Option.toList_some, List.map_append, List.map_singleton]
          isplitl []
          · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ c g => cfgOwn (GF := GF) c g)).2
            isplit
            · iexact Hn'
            · iexact Hc'
          ipureintro; word
        · -- every landing pushed
          have hk : sint.nat k = (landingsL R h.st.st.rv w b full x y).length := by word
          rw [hk, List.take_length]
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _, _, sw'', ncs ++ ncs'
          rw [List.append_assoc]
          iframe
          have hs : settleSuccs (landF R b full x y) h (sint.nat j) =
              (landingsL R h.st.st.rv w b full x y).map land := by
            simp only [settleSuccs, hx, if_neg hdiff, landF, List.map_map]
            rfl
          ihave %Hnl := BigSepL2.bigSepL2_length $$ Hn
          rw [hj1, settleSuccsUpTo_succ, hs]
          isplitl []
          · iapply (BigSepL2.bigSepL2_append
              (Φ := fun _ (c : mcfg) (g : GCfg) => cfgOwn (GF := GF) c g) (Or.inl Hnl)).2
            isplit
            · iexact Hn
            · iexact Hn'
          ipureintro; word
    · -- the inner loop's end: `h` is in the set, its successors in `work`
      have hj : sint.nat j = h.pend.length := by word
      rw [hj]
      wp_for_post
      iframe
      iexists sw', wc ++ ncs, sgs ++ [h], wg ++ settleSuccsUpTo (landF R b full x y) h h.pend.length
      iframe
      isplitl []
      · iapply (BigSepL2.bigSepL2_append
          (Φ := fun _ (c : mcfg) (g : GCfg) => cfgOwn (GF := GF) c g)
          (Or.inl (by omega))).2
        isplit
        · iexact Hwc
        · iexact Hn
      ipureintro; exact setInv_add R b full x y Hok Hinv
  · have Hz : ¬ 0 < sint.Z sw.len := by
      have h0 : sint.Z (W64 0) = 0 := rfl
      rw [h0] at Hif; exact Hif
    have hw0 : wcs = [] := Hw0 Hz
    have hg0 : wgs = [] := List.eq_nil_of_length_eq_zero (by rw [← Hwlen, hw0]; rfl)
    subst hg0
    obtain ⟨h1, h2⟩ := setInv_done Hinv
    iunfold cfgSetOwn at Hset
    icases Hset with ⟨%lsl, %mb, %cs, %B, Hsh, Hsl, Hsb, Hcs, Hcap, #Hcg, %Hcsl, Hb⟩
    (try wp_auto)
    iapply HΦ
    iframe
    isplitl []
    · iexact Hcg
    ipureintro; exact ⟨h1, h2⟩

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
