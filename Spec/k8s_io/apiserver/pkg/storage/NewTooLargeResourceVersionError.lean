/-
`storage.NewTooLargeResourceVersionError(minimumResourceVersion, currentRevision, retrySeconds)`
(`k8s.io/apiserver/pkg/storage/errors.go`): a non-nil error (an `apierrors.NewTimeoutError`, a
`*StatusError`, whose status details carry the "too large resource version" cause): the error
`IsTooLargeResourceVersion` recognizes (`tooLargeErrIs`: its status, details and causes persisted;
strengthened in stage 7e-2, `notes/k8s-7e-2-draft.md` §4.5; the former post, a `*StatusError`,
follows: `apierrors.tooLargeErrIs_ptr`). Lean-first (no Rocq counterpart).
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
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.NewTooLargeResourceVersionError.spec : Prop :=
  ∀ (minRV curRV : w64) (retry : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError))
      (Val #minRV)) (Val #curRV)) (Val #retry))
  {{ (err : GoInterface), RET #err; apierrors.tooLargeErrIs err }}

end spec

end EtcdGrove
end Perennial
