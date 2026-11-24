/-
The proof of `klog.Verbose.InfoS.spec` (`Spec/k8s_io/klog/v2/Verbose__InfoS.lean`), over its
translated body (`klog.go:1496-1500`; klog-infos, 2026-11-23, etcd-grove#25; until then a
trust-boundary axiom, T5-g): when `v` is enabled, `logging.infoS(v.logger, logging.filter, 0, ...)`,
with `v.logger` (`nil`, the premise) and `logging.filter` (`nil` by klog's fact, `klogInit`).
Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.Verbose__InfoS
public import Spec.k8s_io.klog.v2.loggingT__infoS

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

theorem klog.Verbose.InfoS.wp_proof
    (wp_infoS : klog.loggingT.infoS.spec (GF := GF) (hG := hG)) :
    klog.Verbose.InfoS.spec (GF := GF) (hG := hG) := by
  intro v msg args xs dq hv hmsg hok
  wp_start as Hargs
  ihave Hk : (k8s_io.apiserver.pkg.storage.etcd3.klogInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogInit at Hk
  icases Hk with ⟨-, -, -, #Hfilter, -⟩
  wp_auto
  cases hen : v.enabled'
  · try wp_auto
    iapply HΦ
    iframe
  · iStructNamed v
    wp_auto
    wp_apply wp_infoS _ _ _ _ _ _ _ hok hmsg $$ [$Hargs] as Hargs
    · iframe #
      ipureintro
      simp [hv]
    try wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
