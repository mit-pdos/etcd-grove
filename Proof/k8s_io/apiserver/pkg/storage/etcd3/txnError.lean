/-
Lean-first (no Rocq counterpart).

The proof of `txnError`: `err`, or the metrics package's `ErrTransactionConflict` (`metricsInit`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.txnError

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem txnError.wp_proof : txnError.spec (GF := GF) (hG := hG) := by
  intro succeeded err
  wp_start
  ihave #Pm : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Hm : (k8s_io.apiserver.pkg.storage.etcd3.metricsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pm
  icases Hm with ⟨%e, #He⟩
  wp_auto
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ; itrivial
  | nil =>
    cases succeeded <;> wp_auto <;> (iapply HΦ; itrivial)

end proof

end k8s
end EtcdGrove
end Perennial
