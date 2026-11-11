/-
Lean-first (no Rocq counterpart).

The proof of `txnError`: `err`, or the metrics package's `ErrTransactionConflict` (`metricsInit`, an
`errors.New` error: `statusErrOk` by `errorString_statusErrOk`), or `nil`.
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem txnError.wp_proof : txnError.spec (GF := GF) (hG := hG) := by
  intro succeeded err
  wp_start
  ihave #Pm : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Hm : (EtcdGrove.errorsNewVar (GF := GF)
      k8s_io.apiserver.pkg.storage.etcd3.metrics.ErrTransactionConflict go!"transaction conflict") $$ []
  · iapply isPkgInit_access $$ Pm
  iunfold EtcdGrove.errorsNewVar at Hm
  icases Hm with ⟨%x, #Hx, #HM⟩
  wp_auto
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ; iintro #H; iexact H
  | nil =>
    cases succeeded <;> wp_auto
    · iapply HΦ; iintro -
      iapply k8s_io.apiserver.pkg.storage.etcd3.errorString_statusErrOk x _ $$ HM
    · iapply HΦ; iintro #H; iexact H

end proof

end k8s
end EtcdGrove
end Perennial
