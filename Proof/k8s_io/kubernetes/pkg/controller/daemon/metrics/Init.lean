/-
Package initialization of `k8s_io.kubernetes.pkg.controller.daemon.metrics`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates its variables (`metrics.go`: the zero
`registerMetrics`, and `DaemonsetRequeueSkips = metrics.NewCounterVec(...)`), initializes its
imports and runs the translated initializer. **Pending** (`sorry`, Stage 3 of the DaemonSet
run): the `CounterOpts` literal and `NewCounterVec` (component-base, names only: a trust-boundary
spec, it returns some `*CounterVec` and changes no registry).
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Perennial.Proof.sync.Link
public import Proof.k8s_io.component_base.metrics.Init
public import Proof.k8s_io.component_base.metrics.legacyregistry.Init
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
variable [package_sem : _root_.Perennial.k8s_io.kubernetes.pkg.controller.daemon.metrics.Assumptions]

namespace k8s_io.kubernetes.pkg.controller.daemon.metrics

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Once) registerMetrics _ as HregisterMetrics
  wp_apply wp_GlobalAlloc (V := Loc) DaemonsetRequeueSkips _ as HDaemonsetRequeueSkips
  wp_apply (_root_.Perennial.k8s_io.component_base.metrics.legacyregistry.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.k8s_io.component_base.metrics.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of DaemonsetRequeueSkips))
  try wp_auto
  sorry

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.kubernetes.pkg.controller.daemon.metrics

end init

end Perennial
