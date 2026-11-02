/-
Package initialization of `github_com.anishathalye.porcupine`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`linInit`, `Base.lean`): `Linearizability` holds the consistency value whose
oracles slice holds `RealTime` and `GeneralLikely` and whose validity is `RVal` (the closures of
`Closures.lean`). Its initializer runs its variables' translated initializers (func literals,
slice and struct literals).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.anishathalye.porcupine.Assumptions]

namespace github_com.anishathalye.porcupine

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.anishathalye.porcupine get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Consistency) OrderedSequentialConsistency _ as HOrderedSequentialConsistency
  wp_apply wp_GlobalAlloc (V := Consistency) Linearizability _ as HLinearizability
  wp_apply wp_GlobalAlloc (V := Validity) RVal _ as HRVal
  wp_apply wp_GlobalAlloc (V := GoSlice) OrderedSequentialConsistencyOracles _ as HOrderedSequentialConsistencyOracles
  wp_apply wp_GlobalAlloc (V := GoFunc) RealTimeWrites _ as HRealTimeWrites
  wp_apply wp_GlobalAlloc (V := GoSlice) LinearizabilityOracles _ as HLinearizabilityOracles
  wp_apply wp_GlobalAlloc (V := GoFunc) RealTime _ as HRealTime
  wp_apply wp_GlobalAlloc (V := GoFunc) GeneralLikely _ as HGeneralLikely
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of GeneralLikely))
  -- translated initializer of RealTime))
  -- translated initializer of LinearizabilityOracles))
  -- translated initializer of RealTimeWrites))
  -- translated initializer of OrderedSequentialConsistencyOracles))
  -- translated initializer of RVal))
  -- translated initializer of Linearizability))
  -- translated initializer of OrderedSequentialConsistency))
  -- translated initializer of RVal))
  -- translated initializer of OrderedSequentialConsistencyOracles))
  -- translated initializer of RVal))
  -- translated initializer of LinearizabilityOracles))
  -- translated initializer of GeneralLikely))
  -- translated initializer of RealTimeWrites))
  -- translated initializer of RealTime))
  -- translated initializer of GeneralLikely))
  -- translated initializer of RealTime))
  sorry

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.anishathalye.porcupine get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.anishathalye.porcupine

end init

end Perennial
