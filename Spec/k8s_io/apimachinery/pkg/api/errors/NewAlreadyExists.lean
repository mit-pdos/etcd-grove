/-
`apierrors.NewAlreadyExists` (`k8s.io/apimachinery/pkg/api/errors/errors.go`): a 409: the status `Failure`, reason `AlreadyExists`, code 409, with new details. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- `apierrors.NewAlreadyExists(...)`: a 409: the status `Failure`, reason `AlreadyExists`, code 409, with new details. -/
abbrev NewAlreadyExists.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.NewAlreadyExists)) (Val #gr)) (Val #name))
  {{ (p : Loc), RET #p; ∃ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status, p ↦ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗
      ⌜st.Status' = go!"Failure" ∧ st.Reason' = go!"AlreadyExists" ∧ st.Code' = W32 409⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
