/-
`v3rpc.NewQuotaKVServer` (`v3rpc/quota.go`; unit P3b). Lean-first (no Rocq counterpart); the
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewQuotaKVServer(s)`**: a `KVServer` holding a `*quotaKVServer` (`quotaKVServerAt`) over
`NewKVServer(s)`'s `*kvServer` (`kvServerIs`), with the alarmer `{s, "kv"}` (since the fork's
8f793b820, D22g (A): each check builds its quota over the current backend; until then a quota from
`newBackendQuota(s, "kv")` built here, and the member id). The server's logger and quota fields and
the workload premise `backendUnderQuota` go into `quotaAlarmerAt`, for the checks. -/
abbrev v3rpc.NewQuotaKVServer.spec : Prop :=
  ∀ (s : Loc) (A : v3rpc.KVAns GF) (n : w64) (lg : Loc) (qb : w64),
  -- the backend stays under its quota (audit phase B3, D19h)
  apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ v3rpc.raftKV s A ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"MaxTxnOps"
        (structFieldRef EtcdServer go!"Cfg" s) ↦□ n ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ qb }}
    (App (Val (@! v3rpc.NewQuotaKVServer)) (Val #s))
  {{ (kv : GoInterface), RET #kv; ∃ (q p : Loc) (cid mid' : w64),
      ⌜kv = interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q⌝ ∗
      v3rpc.quotaKVServerAt q ⟨go.GoType.PointerType v3rpc.kvServer.ty, #p⟩ s ∗
      v3rpc.kvServerIs p s A cid mid' n }}

end spec

end EtcdGrove
end Perennial
