/-
Lean-first (no Rocq counterpart).

The proof of `storage.NewInternalError`: `err.Error()`, then the composite literal.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.NewInternalError

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.NewInternalError.wp_proof : storage.NewInternalError.spec (GF := GF) (hG := hG) := by
  intro ei
  wp_start as #Hes
  wp_auto
  iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hes
  wp_apply Hes as %s
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
