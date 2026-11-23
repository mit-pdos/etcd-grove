/-
`Model()` (kit.go) meets the register's porcupine model spec `casS` (notes/dsv-gryff.md): the
state's helpers `apply`, `isWrite`, `without`, `with`, `sameCfg`, `hasCfg`, `reach`, `step`,
`equal` over read-only slices, and the pure `stepG_pSeq` (`ModelSet.lean`).
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.ModelSet
public import Dsverify.Proof.gryff.examples.gryffnet.Base
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace gryff.examples.gryffnet

open EtcdGrove EtcdGrove.linkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : gryff.examples.gryffnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.gryff.examples.gryffnet

set_option goose.wp.extras true

/-- `wp_alloc` does not take `#(zero_val w64)` at `go.int64` (the zero value `GoZeroVal go.int64`
steps to): rewritten to `W64 0` inside `wp_auto` (its extra simp set). -/
@[local goose_wp_simp_extra] theorem zero_val_w64 : (zero_val w64 : w64) = W64 0 := rfl

attribute [local goose_wp_simp_extra] OpRead OpWrite OpCAS

/-- `Out{}`. -/
@[local goose_wp_simp_extra] theorem zero_val_Out : (zero_val Out : Out) = outDone := rfl

theorem wp_isWrite (i : In) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! gryff.examples.gryffnet.isWrite)) (Val #i))
    {{ RET #(isWriteG i); True }} := by
  wp_start as #Hk
  wp_auto
  unfold isWriteG
  by_cases h1 : i.Op' = W64 1
  · simp only [h1, _root_.decide_true, Bool.true_or]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h1, _root_.decide_false, Bool.false_or]
    wp_auto
    iapply HΦ; itrivial

theorem wp_apply (v : w64) (i : In) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! gryff.examples.gryffnet.apply)) (Val #v)) (Val #i))
    {{ RET (PairV #(applyG v i).1 #(applyG v i).2); True }} := by
  wp_start as #Hk
  wp_auto
  unfold applyG
  by_cases h1 : i.Op' = W64 1
  · simp only [h1, _root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h1, _root_.decide_false, ↓reduceIte]
    wp_auto
    by_cases h2 : i.Op' = W64 2
    · simp only [h2, _root_.decide_true, ↓reduceIte]
      wp_auto
      by_cases h3 : v = i.A'
      · simp only [h3, _root_.decide_true, ↓reduceIte]
        wp_auto
        iapply HΦ; itrivial
      · simp only [h3, _root_.decide_false, ↓reduceIte]
        wp_auto
        iapply HΦ; itrivial
    · simp only [h2, _root_.decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial

end proof

end gryff.examples.gryffnet
end Perennial
