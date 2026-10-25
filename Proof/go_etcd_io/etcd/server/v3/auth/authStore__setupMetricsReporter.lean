/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__setupMetricsReporter.lean`. Lean-first (no
Rocq counterpart; the auth plan's E2a), as mvcc's `store.setupMetricsReporter`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__setupMetricsReporter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.setupMetricsReporter.wp_proof :
    auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG) := by
  intro st
  wp_start
  ihave Hinit : (authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #G⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (sync.RWMutex.wp_Lock_guard _ _) $$ [$G] as ⟨Hl, HP⟩
  iunfold reportP at HP
  icases HP with ⟨%f, Hf⟩
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hl Hf]
  · inext; iunfold reportP; iexists _; iframe
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
