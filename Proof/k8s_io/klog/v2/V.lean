/-
The proof of `klog.V.spec` (`Spec/k8s_io/klog/v2/V.lean`), over klog's translated `V`, `VDepth`,
`newVerbose` and `Level.get` (klog-leaves, 2026-11-23, etcd-grove#25; until then a trust-boundary
axiom). `VDepth` loads `logging.verbosity` atomically (`Level.get`): at least the level, it returns
`newVerbose(level, true)`; otherwise it loads `logging.filterLength` atomically, 0 by klog's fact
(`klogInit`: no `-vmodule`), and returns `newVerbose(level, false)`, which reads `logging.logger`,
`nil` by the fact, and builds `Verbose{b, nil}`. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.V

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.klog.v2.Assumptions]

/-- `newVerbose(level, b)` with no global logger (`logging.logger` `nil`, klog's fact):
`Verbose{b, nil}`, some `Verbose`. -/
theorem klog.wp_newVerbose (lv : w32) (b : Bool) :
    {{ (k8s_io.apiserver.pkg.storage.etcd3.klogSettingsField (GF := GF) go!"logger" ↦□ null : IProp GF) }}
      (App (App (Val (@! k8s_io.klog.v2.newVerbose)) (Val #lv)) (Val #b))
    {{ (v : k8s_io.klog.v2.Verbose), RET #v; True }} := by
  wp_start as #Hlogger
  wp_auto
  iapply HΦ
  itrivial

theorem klog.V.wp_proof : klog.V.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start
  ihave Hk : (k8s_io.apiserver.pkg.storage.etcd3.klogInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogInit at Hk
  icases Hk with ⟨⟨%vb, #Hverb⟩, #Hflen, #Hlogger⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `Level.get`: the atomic load of `verbosity` (read-only, `vb`)
  wp_apply_core sync.atomic.wp_LoadInt32 $$ [] [-]
  · iexact Hatomic
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists vb
  iframe Hverb
  iintro -
  imod Hmask with -
  imodintro
  wp_auto
  wp_if_destruct
  · -- `-v` at least the level
    wp_apply (klog.wp_newVerbose l true)
    · iexact Hlogger
    iintro %v -
    wp_auto
    iapply HΦ
    itrivial
  · -- below it: the atomic load of `filterLength`, 0 (no `-vmodule`)
    wp_apply_core sync.atomic.wp_LoadInt32 $$ [] [-]
    · iexact Hatomic
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists (W32 0)
    iframe Hflen
    iintro -
    imod Hmask with -
    imodintro
    wp_auto
    wp_apply (klog.wp_newVerbose l false)
    · iexact Hlogger
    iintro %v -
    wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
