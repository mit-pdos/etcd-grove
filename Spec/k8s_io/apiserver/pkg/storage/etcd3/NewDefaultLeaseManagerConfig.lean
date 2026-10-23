/-
`NewDefaultLeaseManagerConfig()` (`lease_manager.go`): the default configuration. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev NewDefaultLeaseManagerConfig.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.NewDefaultLeaseManagerConfig)) (Val #()))
  {{ (cfg : k8s_io.apiserver.pkg.storage.etcd3.LeaseManagerConfig), RET #cfg; True }}

end spec

end k8s
end EtcdGrove
end Perennial
