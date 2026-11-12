/-
`v3rpc.NewQuotaLeaseServer` (`v3rpc/quota.go`; item 4, the server start). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvGrpcStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewQuotaLeaseServer(s)`** returns a new `*quotaLeaseServer` as a `LeaseServer` (over
`NewLeaseServer(s)`, with the alarmer `{s, "lease"}`; as `NewQuotaKVServer`, since D22g (A));
`quotaLeaseServerAt` over `leaseServerAt` (the client lease's stage (c)). -/
abbrev v3rpc.NewQuotaLeaseServer.spec : Prop :=
  ∀ (s : Loc) (A : v3rpc.KVAns GF) (lg0 lg : Loc) (qb : w64),
  -- the backend stays under its quota (audit phase B3, D19h)
  apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.raftKV s A ∗ srvCfgFieldAddr s go!"Logger" ↦□ lg0 ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ qb }}
    (App (Val (@! v3rpc.NewQuotaLeaseServer)) (Val #s))
  {{ (v : GoInterface), RET #v; ∃ (q p : Loc) (cid mid' : w64),
      ⌜v = interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q⌝ ∗
      v3rpc.quotaLeaseServerAt q ⟨go.GoType.PointerType v3rpc.LeaseServer.ty, #p⟩ s ∗
      v3rpc.leaseServerAt p s A cid mid' }}

end spec

end EtcdGrove
end Perennial
