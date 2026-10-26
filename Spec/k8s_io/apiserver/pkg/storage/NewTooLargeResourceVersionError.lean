/-
`storage.NewTooLargeResourceVersionError(minimumResourceVersion, currentRevision, retrySeconds)`
(`k8s.io/apiserver/pkg/storage/errors.go`): a non-nil error (an `apierrors.NewTimeoutError`, a
`*StatusError`, whose status details carry the "too large resource version" cause). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
