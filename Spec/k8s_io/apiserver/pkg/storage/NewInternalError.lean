/-
`storage.NewInternalError(err)` (`k8s.io/apiserver/pkg/storage/errors.go`): an `InternalError`
with `err`'s description. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

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
abbrev storage.NewInternalError.spec : Prop :=
  ∀ (ei : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗
      go_etcd_io.etcd.cache.v3.errorStringSpec ei }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.NewInternalError)) (Val #(GoInterface.ok ei)))
  {{ (ie : k8s_io.apiserver.pkg.storage.InternalError), RET #ie; True }}

end spec

end EtcdGrove
end Perennial
