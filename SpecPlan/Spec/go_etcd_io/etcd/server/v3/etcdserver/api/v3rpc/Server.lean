/-
`v3rpc.Server` (`server/etcdserver/api/v3rpc/`).

Users: 2e's member start (`embed.Etcd`'s `serveClients`, `examples/lib/etcdstart`'s `Serve`): the gRPC server it then starts (`Grpc.start.spec` with `addrAt ep (etcdContract γ ep)`, which is W0's `servesAt γ ep`: `servesAt_addr`) and serves, at the client address `ep` it holds `srvAt s γ ep` for (2e's `srvEp_reserve` at the serving start, which also gives the address's `Http.protoAt`, then `srvAt` from `NewServer`'s `srvFields`: repair3-boot).

Proof sketch: `grpc.CustomCodec(&codec{})` (`codecOk`: the codec's `Marshal`/`Unmarshal` are golang/protobuf's, which call protobuf-go's: `Proto.Marshal.spec`, `Unmarshal.spec`), `Creds` if TLS, `getServerMetrics.spec`, the interceptors (`newLogUnaryInterceptor`, the metrics', `newUnaryInterceptor`, the caller's; the metrics' and `newStreamInterceptor`'s: all `icEtcdOk`/`sicEtcdOk`), `ChainUnaryInterceptor`, `ChainStreamInterceptor`, the size and stream limits (`Grpc`'s option specs), `grpc.NewServer` (`srvBuild`), and each `Register*Server` (3h's generated registrations over `Server.RegisterService.spec` and the generated descriptors, `serviceDescAt`) with the service values (`NewQuotaKVServer`, `NewWatchServer` (2b), `NewQuotaLeaseServer`, `NewClusterServer`, `NewAuthServer`, `NewMaintenanceServer`); the health service (`health.NewServer`, `RegisterHealthServer`: in `B.regs`, its contracts `etcdContract`'s health entries, met by `healthRegs_ok`); `serverMetrics.InitializeMetrics(gs)` (`metricsOk_init`). `regsOk`: for each registration, the generated handler decodes (`decOk_call`) and calls the service's method through the chain (`icChain_call`, `icHandler_call`), each interceptor `icEtcdOk`, the method's `HandlerTriple` (this package's specs), giving `unaryOk`; the streams likewise (`streamOk`, 2b's for `Watch`). Integration X: the registrations hold for the run resource `srvGate s gq` (any share: the caller's `Grpc.start` lends `n` of them, from `srvGate_fractional`, and `GracefulStop` gives them back before 2e's `HardStop`); a handler over 2c's request path passes its share to the server method, the others frame it. The lease handlers (`LeaseGrant`, `LeaseLeases`, `LeaseTimeToLive` and their quota wrappers) take `srvAt s γ ep` (persistent, framed into each registration), which 2c's lease specs need for their `srvLeaseFact`; the other handlers hold for any `ep` and are instantiated at this one.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Server.lean`: over `isServer` and the contracts (was `grpcCfgOk`, `kvRegs`, `authRegs`, ... with `backendUnderQuota`); every service, auth on and off, a TLS configuration, a caller's interceptor that preserves the contracts.

Changes: verify-round relay (server-core's RR request 2): the registrations meet the contracts of
the endpoint the member serves only, `srvAt s γ ep` (was `∀ ep`: as stated, a lagging member's lease
handlers would have given another endpoint's `leaseViewLb`, which 2c's lease specs cannot give).
`ep` is the caller's binder; `srvAt`'s introduction belongs to the serving start (2e's `srvEp_reserve`, repair3-boot).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Server(s, tls, interceptor, gopts...)`: a gRPC server being built whose registrations meet
etcd's contracts at the endpoint `ep` the member `s` serves (`srvAt s γ ep`). -/
def Server.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ep : GoString) (tls : Loc) (ic : GoFunc) (gsl : GoSlice) (gvs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ ∗ srvAt s γ ep ∗ (⌜tls = null⌝ ∨ Transport.tlsCfgOk tls) ∗ (⌜ic = func.nil⌝ ∨ icEtcdOk ic γ) ∗
      gsl ↦*□ gvs ∗ ([∗list] v ∈ gvs, srvOptAt v id) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server)) (Val #s)) (Val #tls)) (Val #ic)) (Val #gsl))
  {{ (gs : Loc), RET #gs; ∃ B : SrvCfg, srvBuild gs B ∗ ∀ (gq : Qp), regsOk B (etcdContract γ ep) (srvGate s gq) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
