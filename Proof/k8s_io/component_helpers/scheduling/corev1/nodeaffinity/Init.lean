/-
Package initialization of `k8s_io.component_helpers.scheduling.corev1.nodeaffinity`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates its variables (`nodeaffinity.go`:
`validSelectorOperators`, `validFieldSelectorOperators`, slice literals of constants), initializes
its imports and runs their translated initializers. **Pending** (`sorry`, Stage 3 of the DaemonSet
run): the slice literals' steps (`wp_slice_literal` over the operator constants).
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.api.core.v1.Init
public import Proof.k8s_io.apimachinery.pkg.fields.Init
public import Proof.k8s_io.apimachinery.pkg.labels.Init
public import Proof.k8s_io.apimachinery.pkg.selection.Init
public import Proof.k8s_io.apimachinery.pkg.util.errors.Init
public import Proof.k8s_io.apimachinery.pkg.util.validation.field.Init
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
variable [package_sem : _root_.Perennial.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

namespace k8s_io.component_helpers.scheduling.corev1.nodeaffinity

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoSlice) validFieldSelectorOperators _ as HvalidFieldSelectorOperators
  wp_apply wp_GlobalAlloc (V := GoSlice) validSelectorOperators _ as HvalidSelectorOperators
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.errors.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.selection.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.labels.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.fields.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.k8s_io.api.core.v1.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of validSelectorOperators))
  -- translated initializer of validFieldSelectorOperators))
  try wp_auto
  sorry

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.component_helpers.scheduling.corev1.nodeaffinity

end init

end Perennial
