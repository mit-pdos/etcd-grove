/-
Lean-first (no Rocq counterpart).

# `SharedModel`'s model and representation (k8s-dist K9 step 4, `notes/k8s-dist-k9.md` §2.1)

- `GoStep R mode c x y e`: one step of `SharedModel`'s `Step` from the configuration `c` on the
  operation `(x, y)` reaches `e`. In mode `Lazy` (0), `c` skipped to the operation's target
  (`targetL`) steps if `stepL` allows it anything; otherwise (and in every other mode) a configuration
  `settle` reaches from `c` (`GoSettle`, `Full` = mode 2) skipped to its target, then `stepL`. The
  model's step reads the output as it is (`y`), `stepL` its plain part (`plainOut y`, as `step`);
- `sharedM g0 R mode`: the model's states are sets of configurations (`GCfg → Prop`), from `{⟨g0, []⟩}`; a step
  keeps every `GoStep` of every configuration, and fails when none is left;
- `SharedBounded B k g`: a configuration of a state made by `k` steps from `g0` is well formed
  (`HWf`), its pending inputs are writes and at most `k`, its revision with its pending writes is at most `2^62 + k`
  (a step lands a write at a revision the operation, `R` or one past the revision names, all below
  `2^62`, or adds one pending write or one revision), and its items with its pending writes at
  most `B + k` (`B` the seeded store's items);
- `RevsBelow x y`: every revision the operation names (`OpAnchors`, and the answer's revision) is
  below `2^62`; `RevsLBelow R`: `R`'s revisions are. (Below `2^62`, not etcd's `2^63`: `settle`
  needs room above a landing for the pending writes, `SettleOk`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open k8s_dist
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj Revs mcfg)

section pure
variable [GooseExts]

/-- One step of `SharedModel`'s `Step` from `c` (see the file header). -/
def GoStep (R : RevsL) (mode : Nat) (c : GCfg) (x : Input) (y : Output) (e : GCfg) : Prop :=
  let lazy := stepL ⟨skipToL c.st (targetL x y (uint.nat c.st.st.rv)), c.pend⟩ x (plainOut y)
  if mode = 0 ∧ lazy ≠ [] then e ∈ lazy
  else ∃ d, GoSettle R (boundL x y) (mode = 2) x y c d ∧
    e ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x (plainOut y)

/-- Every revision `x` and `y` name is below `2^62` (see the file header). -/
def RevsBelow (x : Input) (y : Output) : Prop :=
  OpAnchors (List.range (2 ^ 62)) x y ∧ uint.nat y.RV' < 2 ^ 62

/-- `R`'s revisions are below `2^62`. -/
def RevsLBelow (R : RevsL) : Prop :=
  (∀ a ∈ R.anchors, uint.nat a < 2 ^ 62) ∧ (∀ k, ∀ a ∈ R.byKey k, uint.nat a < 2 ^ 62) ∧
    ∀ k, ∀ a ∈ R.fastByKey k, uint.nat a < 2 ^ 62

/-- A configuration of a state made by `k` steps (see the file header). -/
def SharedBounded (B k : Nat) (g : GCfg) : Prop :=
  HWf g.st ∧ (∀ p ∈ g.pend, isWriteL p = true) ∧ g.pend.length ≤ k ∧
    uint.nat g.st.st.rv + g.pend.length ≤ 2 ^ 62 + k ∧ g.st.st.items.length + g.pend.length ≤ B + k

end pure

/-! ## Lemmas: well-formed histories (moved from `settle.lean`) and `SharedBounded` -/

section lemmas
variable [GooseExts]
open k8s_dist (SettleWith foreignL mstepL_same mstepL_changed advanceL_same advanceL_new)

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

/-- `evMaxL` stays below a bound every revision it reads is below. -/
theorem evMaxL_lt (evs : List WEv) (n : Nat) (hn : 0 < n)
    (h : ∀ e ∈ evs, e.t < 4 → uint.nat e.o.ResourceVersion' < n) : evMaxL evs < n := by
  have key : ∀ (l : List WEv) (t : Nat), t < n → (∀ e ∈ l, uint.nat e.o.ResourceVersion' < n) →
      l.foldl (fun t e => max t (uint.nat e.o.ResourceVersion')) t < n := by
    intro l
    induction l with
    | nil => intro t ht _; exact ht
    | cons e l ih =>
      intro t ht hl
      simp only [List.foldl_cons]
      have := hl e (by simp)
      exact ih _ (by omega) (fun e' he' => hl e' (by simp [he']))
  unfold evMaxL
  exact key _ 0 hn (fun e he => by
    obtain ⟨he, ht⟩ := List.mem_filter.1 he
    exact h e he (by simpa using ht))

/-- **`targetL`'s bound**: on an operation naming revisions below `2^62`, the target is below it. -/
theorem targetL_lt (x : Input) (y : Output) (rv : Nat) (h : RevsBelow x y) :
    targetL x y rv < 2 ^ 62 := by
  obtain ⟨⟨hmin, -, hw, hnw⟩, hy⟩ := h
  simp only [List.mem_range] at hmin hw hnw
  unfold targetL
  split
  · next h5 =>
    split
    · omega
    · next hf =>
      have hwf : y.WFailed' = false := by
        cases hy' : y.WFailed' <;> simp_all
      split
      · omega
      · next evs hevs =>
        have hev := hw h5 hwf evs hevs
        have hm := evMaxL_lt evs (2 ^ 62) (by omega) hev
        split
        · split
          · next req hreq => have := hmin req hreq; omega
          · exact hm
        · exact hm
  · next h5 =>
    obtain ⟨hE, hL, hR, -, -⟩ := hnw h5
    split
    · exact hE
    split
    · omega
    split
    · split
      · omega
      · next req hreq =>
        split
        · exact hmin req hreq
        · exact hL
    split
    · split <;> omega
    · split
      · omega
      · next req hreq => exact hmin req hreq

/-- **`landingsL`'s bound**: a landing is the next revision, or past it and at most `2^62`. -/
theorem landingsL_le (R : RevsL) (rv : w64) (w : Input) (b : w64) (full : Bool) (x : Input)
    (y : Output) (hR : RevsLBelow R) (hy : uint.nat y.RV' < 2 ^ 62)
    (hrv : uint.nat rv + 1 < 2 ^ 64) (l : w64) (hl : l ∈ landingsL R rv w b full x y) :
    l = rv + W64 1 ∨ (uint.nat rv + 1 < uint.nat l ∧ uint.nat l ≤ 2 ^ 62) := by
  obtain ⟨hA, hB, hF⟩ := hR
  have hnext : uint.nat (rv + W64 1) = uint.nat rv + 1 := by word
  have hgt : ∀ r, landOkL rv w b full x y r = true → uint.nat rv + 1 < uint.nat r := by
    intro r hr
    simp only [landOkL, Bool.and_eq_true, decide_eq_true_eq] at hr
    omega
  have hfil : ∀ (S : List w64), (∀ r ∈ S, uint.nat r ≤ 2 ^ 62) →
      l ∈ S.filter (landOkL rv w b full x y) → uint.nat rv + 1 < uint.nat l ∧ uint.nat l ≤ 2 ^ 62 := by
    intro S hS hm
    obtain ⟨hm, hk⟩ := List.mem_filter.1 hm
    exact ⟨hgt l hk, hS l hm⟩
  have hkey : ∀ r ∈ (if full then R.byKey else R.fastByKey) w.Key', uint.nat r ≤ 2 ^ 62 := by
    intro r hr
    cases full
    · have := hF _ r (by simpa using hr); omega
    · have := hB _ r (by simpa using hr); omega
  have hanc : ∀ r ∈ (R.anchors.dropWhile fun a => decide (uint.nat a < uint.nat rv)).flatMap
      (fun a => [a, a + W64 1]), uint.nat r ≤ 2 ^ 62 := by
    intro r hr
    obtain ⟨a, ha, hr⟩ := List.mem_flatMap.1 hr
    have ha' := hA a ((List.dropWhile_sublist _).subset ha)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, _root_.or_false] at hr
    rcases hr with rfl | rfl
    · omega
    · have : uint.nat (a + W64 1) = uint.nat a + 1 := by word
      omega
  have hyl : ∀ r ∈ [y.RV'], uint.nat r ≤ 2 ^ 62 := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr; omega
  have h1 : l ∈ [rv + W64 1] ++ ((if full then R.byKey else R.fastByKey) w.Key').filter
      (landOkL rv w b full x y) →
      (l = rv + W64 1 ∨ (uint.nat rv + 1 < uint.nat l ∧ uint.nat l ≤ 2 ^ 62)) := fun hm => by
    rcases List.mem_append.1 hm with hm | hm
    · exact Or.inl (List.mem_singleton.1 hm)
    · exact Or.inr (hfil _ hkey hm)
  unfold landingsL at hl
  dsimp only at hl
  cases full
  · simp only [Bool.false_eq_true, if_false] at hl h1
    split at hl
    · rcases List.mem_append.1 hl with hm | hm
      · exact h1 hm
      · exact Or.inr (hfil _ hyl hm)
    · exact h1 hl
  · simp only [if_true] at hl h1
    rcases List.mem_append.1 hl with hm | hm
    · split at hm
      · rcases List.mem_append.1 hm with hm | hm
        · exact h1 hm
        · exact Or.inr (hfil _ hyl hm)
      · exact h1 hm
    · exact Or.inr (hfil _ hanc hm)

/-- `SharedBounded` through a skip to a target below `2^62`. -/
theorem sharedBounded_skipTo (B k t : Nat) (g : GCfg) (ht : t < 2 ^ 62)
    (hg : SharedBounded B k g) : SharedBounded B k ⟨skipToL g.st t, g.pend⟩ := by
  obtain ⟨hw, hp, hpk, hrv, hit⟩ := hg
  have h1 := k8s_dist.skipToL_rv g.st t (by omega)
  have h2 := k8s_dist.skipToL_items g.st t
  refine ⟨hwf_skipToL _ _ hw (by omega), hp, hpk, ?_, ?_⟩
  · simp only; rw [h1]; omega
  · simp only; rw [h2]; omega

/-- `SharedBounded` through `stepL`, one more. -/
theorem sharedBounded_stepL (B k : Nat) (g : GCfg) (x : Input) (y : Output) (hk : k < 2 ^ 60)
    (hg : SharedBounded B k g) (e : GCfg) (he : e ∈ stepL g x y) : SharedBounded B (k + 1) e := by
  obtain ⟨hw, hp, hpk, hrv, hit⟩ := hg
  unfold stepL at he
  split at he
  · split at he
    · simp only [List.mem_singleton] at he; subst he
      exact ⟨hw, hp, by omega, by omega, by omega⟩
    · cases he
  split at he
  · split at he
    · next hx =>
      simp only [List.mem_singleton] at he; subst he
      refine ⟨hw, ?_, ?_, ?_, ?_⟩
      · intro p hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact hx
        · exact hp p hp'
      all_goals simp only [List.length_cons]; omega
    · simp only [List.mem_singleton] at he; subst he
      exact ⟨hw, hp, by omega, by omega, by omega⟩
  · split at he
    · simp only [List.mem_singleton] at he; subst he
      have hl := kstepL_length x g.st
      have hrl := kstepL_rv_le x g.st (Nat.le_of_eq hw.1.symm)
      have hwf : HWf (kstepL x g.st).1 := by
        cases hxw : isWriteL x
        · rw [k8s_dist.kstepL_nonwrite x g.st hxw]; exact hw
        · exact hwf_kstepL x g.st hw hxw (by omega)
      have hh := hw.1
      refine ⟨hwf, hp, by simp only; omega, ?_, ?_⟩
      · simp only; omega
      · simp only; omega
    · cases he

/-- `SharedBounded` through `settle` (`GoSettle`). -/
theorem sharedBounded_settle (R : RevsL) (b : w64) (full : Bool) (x : Input) (y : Output)
    (B k : Nat) (hk : k < 2 ^ 60) (hR : RevsLBelow R) (hy : uint.nat y.RV' < 2 ^ 62) {c d : GCfg}
    (hs : GoSettle R b full x y c d) (hc : SharedBounded B k c) : SharedBounded B k d := by
  revert hc
  induction hs with
  | refl => exact id
  | @drop c d i hi hrv _ ih =>
    intro hc
    apply ih
    obtain ⟨hw, hp, hpk, hrvb, hit⟩ := hc
    have hlen := length_removeAtL _ i hi
    refine ⟨hw, fun p hp' => hp p (mem_removeAtL hp'), ?_, ?_, ?_⟩ <;> simp only <;> omega
  | @land c d i l hi hrv hl _ ih =>
    intro hc
    apply ih
    obtain ⟨hw, hp, hpk, hrvb, hit⟩ := hc
    have hlen := length_removeAtL c.pend i hi
    have hpw : ∀ p ∈ removeAtL c.pend i, isWriteL p = true := fun p hp' => hp p (mem_removeAtL hp')
    have hx : isWriteL (pendAt c i) = true := by
      rw [pendAt_eq c i hi]; exact hp _ (List.getElem_mem hi)
    obtain ⟨lw, hlw, rfl⟩ := List.mem_map.1 hl
    have hrv1 : uint.nat (c.st.st.rv + W64 1) = uint.nat c.st.st.rv + 1 := by word
    have hm := landingsL_le R c.st.st.rv (pendAt c i) b full x y hR hy (by omega) lw hlw
    have hge : uint.nat c.st.st.rv + 1 ≤ uint.nat lw := by
      rcases hm with h | h
      · rw [h]; omega
      · omega
    have hle : uint.nat lw + c.pend.length ≤ 2 ^ 62 + k + 1 := by
      rcases hm with h | h
      · rw [h, hrv1]; omega
      · omega
    have hw' : HWf (skipToL c.st (uint.nat lw - 1)) := hwf_skipToL _ _ hw (by omega)
    have hrv' : uint.nat (skipToL c.st (uint.nat lw - 1)).st.rv = uint.nat lw - 1 := by
      rw [k8s_dist.skipToL_rv _ _ (by omega)]; omega
    have hit' : (skipToL c.st (uint.nat lw - 1)).st.items = c.st.st.items :=
      k8s_dist.skipToL_items _ _
    have hk' := kstepL_write (pendAt c i) (skipToL c.st (uint.nat lw - 1)) hx
    have hst : (kstepL (pendAt c i) (skipToL c.st (uint.nat lw - 1))).1.st =
        (mstepL (pendAt c i) (skipToL c.st (uint.nat lw - 1)).st).1 := by
      rw [hk']; exact advanceL_items _ _
    have hil := mstepL_length (pendAt c i) (skipToL c.st (uint.nat lw - 1)).st
    have hrvl : uint.nat (mstepL (pendAt c i) (skipToL c.st (uint.nat lw - 1)).st).1.rv ≤
        uint.nat lw := by
      rcases mstepL_rv (pendAt c i) (skipToL c.st (uint.nat lw - 1)).st with h | h <;> rw [h]
      · omega
      · word
    refine ⟨hwf_kstepL _ _ hw' hx (by omega), hpw, ?_, ?_, ?_⟩
    · simp only; omega
    · simp only; rw [hst]; omega
    · simp only; rw [hst]; rw [hit'] at hil; omega

/-- `SharedBounded` through one step of the model, one more. -/
theorem sharedBounded_goStep (R : RevsL) (mode B k : Nat) (c e : GCfg) (x : Input) (y : Output)
    (hk : k < 2 ^ 60) (hR : RevsLBelow R) (hxy : RevsBelow x y) (hc : SharedBounded B k c)
    (he : GoStep R mode c x y e) : SharedBounded B (k + 1) e := by
  unfold GoStep at he
  dsimp only at he
  split at he
  · exact sharedBounded_stepL B k _ x _ hk
      (sharedBounded_skipTo B k _ c (targetL_lt x y _ hxy) hc) e he
  · obtain ⟨d, hd, he⟩ := he
    have hdb := sharedBounded_settle R _ _ x y B k hk hR hxy.2 hd hc
    exact sharedBounded_stepL B k _ x _ hk
      (sharedBounded_skipTo B k _ d (targetL_lt x y _ hxy) hdb) e he

/-- `SharedBounded` gives `settle`'s premise. -/
theorem sharedBounded_settleOk (R : RevsL) (y : Output) (B k : Nat) (hB : B < 2 ^ 61)
    (hk : k < 2 ^ 60) (hR : RevsLBelow R) (hy : uint.nat y.RV' < 2 ^ 62) (g : GCfg)
    (hg : SharedBounded B k g) : SettleOk R y g := by
  obtain ⟨hw, hp, hpk, hrv, hit⟩ := hg
  obtain ⟨hA, hBk, hF⟩ := hR
  refine ⟨fun a ha => ?_, fun k' a ha => ?_, fun k' a ha => ?_, by omega, by omega, by omega, hp⟩
  · have := hA a ha; omega
  · have := hBk k' a ha; omega
  · have := hF k' a ha; omega

/-- `SharedBounded` gives `stepIdx`'s premise. -/
theorem sharedBounded_stepIdxOk (x : Input) (y : Output) (B k : Nat) (hB : B < 2 ^ 61)
    (hk : k < 2 ^ 60) (hxy : RevsBelow x y) (g : GCfg) (hg : SharedBounded B k g) :
    g.st.st.items.length + 1 < 2 ^ 63 ∧ g.pend.length + 1 < 2 ^ 63 ∧
      g.st.hist.length + 1 < 2 ^ 64 ∧
      (x.Kind' = W64 5 → uint.Z g.st.st.rv < 2 ^ 63 ∧
        ∀ n, parseRVD x.MinRV' = some n → uint.Z n < 2 ^ 63) ∧
      (x.Kind' = W64 5 → HWf g.st) := by
  obtain ⟨hw, hp, hpk, hrv, hit⟩ := hg
  have hmin := hxy.1.1
  simp only [List.mem_range] at hmin
  have hh := hw.1
  refine ⟨by omega, by omega, by omega, fun _ => ⟨?_, fun n hn => ?_⟩, fun _ => hw⟩
  · have : uint.nat g.st.st.rv < 2 ^ 63 := by omega
    word
  · have := hmin n hn
    word

end lemmas

section go
variable [GooseExts] [go_gctx : GoGlobalContext]

open Classical in
/-- Porcupine's operation as the input and output it boxes, if it is one. -/
def decIO (io : github_com.anishathalye.porcupine.OpV) : Option (Input × Output) :=
  if h : ∃ p : Input × Output, io = (boxIn p.1, boxOut p.2) then some h.choose else none

open Classical in
/-- **`SharedModel`'s sequential model** (see the file header). -/
def sharedM (g0 : HSt) (R : RevsL) (mode : Nat) :
    github_com.anishathalye.porcupine.Theory.SeqModel (GCfg → Prop) github_com.anishathalye.porcupine.OpV where
  init := fun g => g = ⟨g0, []⟩
  step S io := match decIO io with
    | none => none
    | some (x, y) =>
      let S' : GCfg → Prop := fun e => ∃ c, S c ∧ GoStep R mode c x y e
      if ∃ e, S' e then some S' else none

end go

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `v` is a `state` whose configurations are exactly `S` (a configuration may be listed more than
once), each `SharedBounded B k`. -/
def sharedRep (B k : Nat) (v : GoInterface) (S : GCfg → Prop) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List mcfg) (gs : List GCfg),
    ⌜v = boxSt sl ∧ (∀ g, S g ↔ g ∈ gs) ∧ ∀ g ∈ gs, SharedBounded B k g⌝ ∗ sl ↦*□ cs ∗
      [∗list] c;g ∈ cs;gs, cfgOwn c g)

instance sharedRep_persistent (B k : Nat) (v : GoInterface) (S : GCfg → Prop) :
    Persistent (sharedRep (GF := GF) B k v S) := by
  unfold sharedRep; infer_instance

/-- **`SharedModel`'s specification**: `sharedM`, its states' values `sharedRep` (with the seeded
store's items as `B`), on operations naming revisions below `2^62`. -/
def sharedS (g0 : HSt) (R : RevsL) (mode : Nat) :
    github_com.anishathalye.porcupine.ModelSpec GF (GCfg → Prop) where
  M := sharedM g0 R mode
  rep k := sharedRep g0.st.items.length k
  ioOk i o := iprop(∃ x y, ⌜i = boxIn x ∧ o = boxOut y ∧ RevsBelow x y⌝)
  ioOk_pers _ _ := by infer_instance

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
