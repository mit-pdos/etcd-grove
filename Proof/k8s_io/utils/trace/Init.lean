/-
Package initialization of `k8s_io.utils.trace`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers: `klogV`, a func literal over `klog.V(lvl).Enabled()` (prove-k8s,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.klog.v2.Init
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
variable [package_sem : _root_.Perennial.k8s_io.utils.trace.Assumptions]

namespace k8s_io.utils.trace

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.utils.trace get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.trace }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) klogV _ as HklogV
  wp_apply (_root_.Perennial.k8s_io.klog.v2.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of klogV))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.utils.trace get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.trace }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.utils.trace

end init

end Perennial
