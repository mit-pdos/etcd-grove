/-
The proof of `klog.Errorf.spec` (`Spec/k8s_io/klog/v2/Errorf.lean`), over klog's translated `Errorf`
(`klog.go:1641-1643`): `logging.printf` at `ErrorLog` with `logging.logger` and `logging.filter`, both `nil`
by klog's fact (`klogInit`). klog-printf, 2026-11-23, etcd-grove#25; until then a trust-boundary
axiom. Lean-first.
-/
module

public import Spec.k8s_io.klog.v2.Errorf
public import Spec.k8s_io.klog.v2.loggingT__printf

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

theorem klog.Errorf.wp_proof
    (wp_printf : klog.loggingT.printf.spec (GF := GF) (hG := hG)) :
    klog.Errorf.spec (GF := GF) (hG := hG) := by
  intro f args xs dq
  wp_start as ⟨Hargs, Hok⟩
  ihave Hk : (k8s_io.apiserver.pkg.storage.etcd3.klogInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogInit at Hk
  icases Hk with ⟨-, -, #Hlogger, #Hfilter, -⟩
  wp_auto
  wp_apply wp_printf $$ [$Hargs $Hok] as ⟨Hargs, Hok⟩
  · iframe #
    ipureintro
    simp
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
