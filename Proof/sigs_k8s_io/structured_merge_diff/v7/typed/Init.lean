/-
Package initialization of `sigs_k8s_io.structured_merge_diff.v7.typed`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True` (`Base.lean`). Its initializer allocates its translated variables,
initializes its imports, sets them (`ruleKeepRHS`, a function value; the walker pools `fmPool`,
`tPool`, `cmpwPool`, `mwPool`, `vPool`, `sync.Pool` literals with a `New` function) and runs the
trusted initializers of `ssParser` and `DeducedParseableType`
(`TrustedCode/sigs_k8s_io/structured_merge_diff/v7/typed.lean`: models that do nothing).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Init
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
variable [package_sem : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace sigs_k8s_io.structured_merge_diff.v7.typed

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) vPool _ as HvPool
  wp_apply wp_GlobalAlloc (V := _) mwPool _ as HmwPool
  wp_apply wp_GlobalAlloc (V := _) cmpwPool _ as HcmpwPool
  wp_apply wp_GlobalAlloc (V := _) tPool _ as HtPool
  wp_apply wp_GlobalAlloc (V := _) fmPool _ as HfmPool
  wp_apply wp_GlobalAlloc (V := _) ruleKeepRHS _ as HruleKeepRHS
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ruleKeepRHS))
  try wp_auto
  wp_call  -- ssParser: its trusted initializer does nothing
  wp_call  -- DeducedParseableType: its trusted initializer does nothing
  -- translated initializer of fmPool))
  repeat (first | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto) | wp_auto)
  -- translated initializer of tPool))
  -- translated initializer of cmpwPool))
  -- translated initializer of mwPool))
  -- translated initializer of vPool))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end sigs_k8s_io.structured_merge_diff.v7.typed

end init

end Perennial
