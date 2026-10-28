/-
`Serve(s, addr)` (`examples/common/common.go`; 2026-10-22, D33): a started member's gRPC API served
on a listener at `addr` -- `v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(...))` (the
clients' keepalive pings allowed every 5s, as etcd's `embed`; since 2026-10-23,
`notes/client-timeouts-plan.md` D-T5, as linkv3p's `startMember` since D28), `net.Listen("tcp",
addr)`, `go gs.Serve(l)`; what the examples' `Main`s did after `Start`. Lean-first (no Rocq
counterpart). The policy is a neutral server option (D28's trust-boundary axiom
`grpc.KeepaliveEnforcementPolicy`): the triple does not mention it.

**The triple:** from a started member's views and serving resources (`memberUp`'s, at its apply
environment `E`, request names `ρ`, read names `γr` and configuration `cfg`), the right to listen
on `addr` (`netAddrFree`), and the **caller's ghost step** `G` from what `v3rpc.Server` and
`Listen` return (`grpcUp`) to the right to serve (`grpcServeTok`) and the caller's `Q`: an error,
or `Q` at the KV server's cluster and member ids and the watch server's state. The ghost step is the
caller's because what it registers at the address differs among the examples (etcd's KV calls,
`client.etcd_kv_started`; with the watch server's facts, watchkv's `wk_served`; with the member's
refusal-freedom first, `etcd_noRefusal`); it is a wand, which may hold the caller's own resources
(the request slots `memberUp` left) in its closure.

**The pure premises:** the configuration's logger not `nil`, no tracer options, no progress-notify
interval (`memberUp`'s); `v3rpc.Server`'s (the gRPC service values' method sets, the backend under
its quota).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev Serve.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (s : Loc) (addr : GoString)
    (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (Q : w64 → w64 → v3rpc.WSrv GF → IProp GF),
  cfg.Logger' ≠ null → cfg.TracerOptions' = slice.nil → cfg.WatchProgressNotifyInterval' = 0 →
  v3rpc.ServerMethodSets → apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      netAddrFree (GF := GF) addr ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗ srvWatchReaders s E 64 ∗
      v3rpc.runsNoRequireLeader ∗
      srvLgReader s ∗ srvBemuReader s ∗ srvGoRes s ∗
      srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ cfg.WatchProgressNotifyInterval' ∗
      (∀ (gs : Loc) (lis : GoInterface) (cid mid : w64) (R : v3rpc.WSrv GF),
        grpcUp s E ρ γr gs lis addr cid mid R ={⊤}=∗ grpcServeTok gs lis ∗ Q cid mid R) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Serve))
      (Val #s)) (Val #addr))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (cid mid : w64) (R : v3rpc.WSrv GF), Q cid mid R) }}

end spec

end common
end EtcdGrove
end Perennial
