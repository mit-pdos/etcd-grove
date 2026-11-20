/-
The proof of `storage.IsNotFound`: `isErrCode(err, ErrCodeKeyNotFound)`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.IsNotFound
public import Spec.k8s_io.apiserver.pkg.storage.isErrCode

@[expose] public section

set_option linter.iris.style.nameCheck false
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
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.IsNotFound.wp_proof (wp_isErrCode : storage.isErrCode.spec (GF := GF) (hG := hG)) :
    storage.IsNotFound.spec (GF := GF) (hG := hG) := by
  intro err dq c
  wp_start as H
  (try wp_auto)
  wp_apply wp_isErrCode err dq c (W64 1) $$ [$H] as H
  (try wp_auto)
  iapply HΦ
  iexact H

end proof

end EtcdGrove
end Perennial
