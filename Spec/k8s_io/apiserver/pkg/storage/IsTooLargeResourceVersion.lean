/-
`storage.IsTooLargeResourceVersion(err)` (`k8s.io/apiserver/pkg/storage/errors.go:259-265`): on an
error seen as `w` (`apierrors.apiErrAt`), `tooLargeV w`: a timeout `*StatusError` whose details list
the `ResourceVersionTooLarge` cause; `false` of a plain error. Proved from the translated body and
`apierrors.IsTimeout`'s and `HasStatusCause`'s trusted specs (stage 7e-2, `notes/k8s-7e-2-draft.md`
§4.5). Lean-first (no Rocq counterpart).
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
variable [errors_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- See the file header. -/
abbrev storage.IsTooLargeResourceVersion.spec : Prop :=
  ∀ (err : GoInterface) (w : apierrors.ApiErrView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ apierrors.apiErrAt err w }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion)) (Val #err))
  {{ RET #(apierrors.tooLargeV w); True }}

end spec

end EtcdGrove
end Perennial
