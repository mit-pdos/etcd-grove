/-
`apierrors.NewTimeoutError(message, retryAfterSeconds)` (`k8s.io/apimachinery/pkg/api/errors/
errors.go`): a new `*StatusError` whose status is a failure (`"Failure"`, reason `"Timeout"`,
code 504), with new status details (owned: the caller may set their causes, as
`storage.NewTooLargeResourceVersionError` does), with no causes yet (`Causes` `nil`: a caller that
sets none persists them into `apierrors.statusDetailsAt st []`, `statusDetailsAt_nil`; the
apierrors-fix stage, 2026-11-17) and `RetryAfterSeconds` `int32(retryAfterSeconds)` (k8s 7g: what
`SuggestsClientDelay` reads). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Proof.k8s_io.apimachinery.pkg.api.errors.View

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- See the file header. -/
abbrev apierrors.NewTimeoutError.spec : Prop :=
  ∀ (message : GoString) (retry : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.NewTimeoutError)) (Val #message))
      (Val #retry))
  {{ (p : Loc), RET #p; ∃ (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
        (dv : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusDetails),
      p ↦ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗ st.Details' ↦ dv ∗ ⌜dv.Causes' = slice.nil⌝ ∗
      ⌜st.Status' = go!"Failure" ∧ st.Reason' = go!"Timeout" ∧ st.Code' = W32 504⌝ ∗
      ⌜dv.RetryAfterSeconds' = W32 (sint.Z retry)⌝ }}

end spec

end EtcdGrove
end Perennial
