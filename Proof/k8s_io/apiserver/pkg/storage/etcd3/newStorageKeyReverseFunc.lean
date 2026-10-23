/-
Lean-first (no Rocq counterpart).

The proof of `newStorageKeyReverseFunc`: a closure.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.newStorageKeyReverseFunc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem newStorageKeyReverseFunc.wp_proof : newStorageKeyReverseFunc.spec (GF := GF) (hG := hG) := by
  intro pp rk
  wp_start
  wp_auto
  cases decide (rk = func.nil)
  · wp_auto
    rw [recv_eq_func_mk]
    iapply HΦ
    itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end k8s
end EtcdGrove
end Perennial
