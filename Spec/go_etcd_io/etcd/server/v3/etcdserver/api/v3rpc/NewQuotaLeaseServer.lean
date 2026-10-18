/-
`v3rpc.NewQuotaLeaseServer` (`v3rpc/quota.go`; item 4, the server start). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvGrpcStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart

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

/-- **`NewQuotaLeaseServer(s)`** returns a new `*quotaLeaseServer` as a `LeaseServer` (over
`NewLeaseServer(s)`, with `newBackendQuota(s, "lease")`, the alarmer `s` and its member id);
the reader slots come back. -/
abbrev v3rpc.NewQuotaLeaseServer.spec : Prop :=
  ∀ (s : Loc) (A : v3rpc.KVAns GF) (lg0 lg : Loc) (qb mid : w64),
  -- the backend stays under its quota (audit phase B3, D19h)
  apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.raftKV s A ∗ srvCfgFieldAddr s go!"Logger" ↦□ lg0 ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ qb ∗ srvBemuReader s ∗
      srvMemberIDAddr s ↦□ mid }}
    (App (Val (@! v3rpc.NewQuotaLeaseServer)) (Val #s))
  {{ (v : GoInterface), RET #v; ∃ q : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q⌝ ∗
      srvLgReader s ∗ srvBemuReader s }}

end spec

end EtcdGrove
end Perennial
