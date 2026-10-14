/-
`v3rpc.newBackendQuota` (`v3rpc/quota.go`; unit P3b). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvQuota.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`newBackendQuota(s, name)`**: `storage.NewBackendQuota(s.Logger(),
s.Cfg.QuotaBackendBytes, s.Backend(), name)`, a quota (`apply.isQuota`); the reader slots of
`lgMu` and `bemu` come back. -/
abbrev v3rpc.newBackendQuota.spec : Prop :=
  ∀ (s lg : Loc) (qb : w64) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ qb ∗ srvBemuReader s }}
    (App (App (Val (@! v3rpc.newBackendQuota)) (Val #s)) (Val #name))
  {{ (qv : GoInterface), RET #qv; apply.isQuota qv ∗ srvLgReader s ∗ srvBemuReader s }}

end spec

end EtcdGrove
end Perennial
