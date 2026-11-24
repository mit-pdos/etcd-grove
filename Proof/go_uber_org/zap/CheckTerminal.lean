/-
`zap.Logger.check` at `PanicLevel` and `FatalLevel` on a `NewNop` logger (zap-z2, 2026-11-23), what
`Logger.Panic` and `Logger.Fatal` run: the level test is skipped (`lvl ≥ DPanicLevel`), the entry is
built (`log.name`, `log.clock.Now()`), the no-op core's `Check` returns `nil`, and `After` takes a fresh
entry from zapcore's `_cePool` (`getCheckedEntry`, `reset`) with the terminal hook (`WriteThenPanic` or
`WriteThenFatal`: the logger's `onPanic`/`onFatal` are `nil`). Not a spec of `check` (whose spec stops below
`DPanicLevel`): a lemma over its body and its callees' specs, for the two proofs.
-/
module

public import Spec.go_uber_org.zap.Defs
public import Spec.go_uber_org.zap.internal.pool.Pool__Get
public import Perennial.Proof.time.Link
public import Proof.go_uber_org.zap.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_uber_org

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_uber_org.zap.Assumptions]

/-- The terminal entry `check` returns at level `lvl` (`PanicLevel` 4 or `FatalLevel` 5): owned, not
dirty, its message `msg`, its hook the level's `CheckWriteAction` (`WriteThenPanic` 2, `WriteThenFatal`
3), no `before` hooks and no cores (both slices of length 0; never returned to the pool: the hook
panics or exits first). -/
def zap.terminalEntry (ce : Loc) (msg : GoString) (act : w8) : IProp GF :=
  iprop(∃ v : go_uber_org.zap.zapcore.CheckedEntry, ce ↦ v ∗
    ⌜ce ≠ null ∧ v.dirty' = false ∧ v.Entry'.Message' = msg ∧
      v.after' = interface.mkOk go_uber_org.zap.zapcore.CheckWriteAction.ty #act ∧
      sint.Z v.before'.len = 0 ∧ sint.Z v.cores'.len = 0⌝)

/-- A slice's capacity is not negative, given its ownership. -/
theorem zap.ownSlice_cap_nonneg {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (vs : List V) (dq : DFrac) : (s ↦*{dq} vs : IProp GF) ⊢ ⌜0 ≤ sint.Z s.cap⌝ := by
  iintro Hs
  ihave %Hl := ownSlice_len s dq vs $$ Hs
  rw [ownSlice_unseal]; unfold ownSliceDef
  icases Hs with (%H | ⟨-, %Hc⟩)
  · ipureintro; obtain ⟨rfl, -⟩ := H; decide
  · ipureintro; omega

theorem zap.wp_check_terminal
    (wp_Get : zap.internal.pool.Pool.Get.spec (GF := GF) (hG := hG))
    (l : Loc) (lvl act : w8) (msg : GoString) (hlvl : (lvl = W8 4 ∧ act = W8 2) ∨ (lvl = W8 5 ∧ act = W8 3)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ zapLoggerOk l }}
      (App (App (Val (l @!! go.GoType.PointerType go_uber_org.zap.Logger.ty @!! go!"check")) (Val #lvl)) (Val #msg))
    {{ (ce : Loc), RET #ce; zap.terminalEntry ce msg act }} := by
  wp_start as #Hok
  unfold zapLoggerOk zap.nopLogger
  icases Hok with ⟨%Hnn, #⟨#Hcore, #Hdev, #Hac, #Hpan, #Hfat, ⟨%nm, #Hname⟩, ⟨%c, #Hclk⟩⟩⟩
  ihave #Hzc : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore $$ []
  · iPkgInit
  ihave #Hzci := _root_.Perennial.go_uber_org.zap.zapcore.isInit_access $$ Hzc
  icases Hzci with ⟨-, ⟨%pce, #Hpce, #Hpool⟩⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  have hge : ¬ (sint.Z lvl < sint.Z (W8 3)) := by
    rcases hlvl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  rw [decide_eq_false hge]
  wp_auto
  -- `log.clock.Now()`: `systemClock.Now` is `time.Now()`
  wp_method_call
  wp_call
  wp_auto
  wp_apply time.wp_Now as %t -
  try wp_auto
  -- the no-op core's `Check` returns its `nil` entry
  wp_method_call
  wp_call
  wp_auto
  rcases hlvl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    try wp_auto
    -- `terminalHookOverride(WriteThenPanic, nil)` is `WriteThenPanic` (`WriteThenFatal` likewise)
    wp_func_call
    wp_call
    try wp_auto
    -- `After` on the `nil` entry: `getCheckedEntry()`
    wp_method_call
    wp_call
    try wp_auto
    wp_func_call
    wp_call
    try wp_auto
    wp_apply wp_Get _ pce zapcore.pooledEntry $$ [$Hpool] as %e He
    unfold zapcore.pooledEntry
    icases He with ⟨%v, Hv, ⟨%bs, Hb⟩, ⟨%cs, Hc⟩⟩
    try wp_auto
    -- `reset`
    wp_method_call
    wp_call
    try wp_auto
    isimp only at Hv
    ihave %Hcn := ownSlice_len $$ Hc
    rename_i ki
    ihave HI : (∃ (j : w64) (xs : List GoInterface),
        "i" ∷ i_ptr ↦ j ∗ "Hc" ∷ v.cores' ↦* xs ∗
        "%Hj" ∷ ⌜xs.length = sint.nat v.cores'.len ∧ 0 ≤ sint.Z j⌝ : IProp GF) $$ [i Hc]
    · iexists W64 0, cs
      iframe
      ipureintro
      exact ⟨Hcn.1, by decide⟩
    ihave HK : (∃ k : w64, ki ↦ k : IProp GF) $$ [i]
    · iexists _; iexact i
    wp_for HI
    icases HK with ⟨%k, HK⟩
    by_cases Hlt : sint.Z j < sint.Z v.cores'.len
    · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      have hjl : (sint.Z j).toNat < xs.length := by
        have h4 : sint.nat v.cores'.len = (sint.Z v.cores'.len).toNat := rfl
        have := Hj.1; omega
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.cores'.len := ⟨Hj.2, Hlt⟩
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index v.cores' (sint.Z j) xs (DFrac.own 1) (xs[(sint.Z j).toNat]'hjl)
        Hj.2 $$ [Hc] as Hc
      · iframe; ipureintro; exact List.getElem?_eq_getElem hjl
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply (wp_store_slice_index (V := GoInterface) v.cores' (sint.Z j) xs GoInterface.nil) $$ [Hc] as Hc
      · iframe; ipureintro; omega
      (try wp_auto)
      wp_for_post
      iframe
      isplitl [i Hc]
      · iexists j + W64 1, _
        iframe
        ipureintro; constructor
        · rw [List.length_set]; exact Hj.1
        · word
      · iexists _; iexact HK
    · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      ihave %Hccap := zap.ownSlice_cap_nonneg $$ Hc
      have hs0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
          sint.Z (W64 0) ≤ sint.Z v.cores'.cap := ⟨by decide, by decide, Hccap⟩
      simp only [hs0, _root_.and_self, ↓reduceIte]
      (try wp_auto)
      isimp only at Hv
      ihave %Hbn := ownSlice_len $$ Hb
      rename_i kb
      ihave HI2 : (∃ (j : w64) (ys : List GoFunc),
          "i" ∷ i_ptr ↦ j ∗ "Hb" ∷ v.before' ↦* ys ∗
          "%Hj" ∷ ⌜ys.length = sint.nat v.before'.len ∧ 0 ≤ sint.Z j⌝ : IProp GF) $$ [i Hb]
      · iexists W64 0, bs
        iframe
        ipureintro
        exact ⟨Hbn.1, by decide⟩
      ihave HK2 : (∃ k : w64, kb ↦ k : IProp GF) $$ [i]
      · iexists _; iexact i
      wp_for HI2
      icases HK2 with ⟨%k2, HK2⟩
      by_cases Hlt2 : sint.Z j < sint.Z v.before'.len
      · rw [decide_eq_true Hlt2]; simp only [↓reduceIte]
        have hjl : (sint.Z j).toNat < ys.length := by
          have h4 : sint.nat v.before'.len = (sint.Z v.before'.len).toNat := rfl
          have := Hj.1; omega
        have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.before'.len := ⟨Hj.2, Hlt2⟩
        (try wp_auto)
        (try simp only [hb, _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index v.before' (sint.Z j) ys (DFrac.own 1) (ys[(sint.Z j).toNat]'hjl)
          Hj.2 $$ [Hb] as Hb
        · iframe; ipureintro; exact List.getElem?_eq_getElem hjl
        (try wp_auto)
        (try simp only [hb, _root_.and_self, ↓reduceIte])
        wp_apply (wp_store_slice_index (V := GoFunc) v.before' (sint.Z j) ys func.nil) $$ [Hb] as Hb
        · iframe; ipureintro; omega
        (try wp_auto)
        wp_for_post
        iframe
        isplitl [i Hb]
        · iexists j + W64 1, _
          iframe
          ipureintro; constructor
          · rw [List.length_set]; exact Hj.1
          · word
        · iexists _; iexact HK2
      · rw [decide_eq_false Hlt2]; simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        ihave %Hbcap := zap.ownSlice_cap_nonneg $$ Hb
        have hs1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
            sint.Z (W64 0) ≤ sint.Z v.before'.cap := ⟨by decide, by decide, Hbcap⟩
        simp only [hs1, _root_.and_self, ↓reduceIte]
        (try wp_auto)
        isimp only at Hv
        ihave %Hen := typedPointsto_not_null _ _ _ $$ Hv
        iapply HΦ
        unfold zap.terminalEntry
        iexists _
        iframe
        ipureintro
        exact ⟨Hen, rfl, rfl, rfl, by simp [slice.slice], by simp [slice.slice]⟩

end lemmas

end EtcdGrove
end Perennial
