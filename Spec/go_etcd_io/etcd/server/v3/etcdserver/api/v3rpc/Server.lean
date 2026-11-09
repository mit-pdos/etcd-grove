/-
`v3rpc.Server` (`server/etcdserver/api/v3rpc/`).

Users: 2e's member start (`embed.Etcd`'s `serveClients`, `examples/lib/etcdstart`'s `Serve`): the gRPC server it then starts (`Grpc.start.spec` with `addrAt ep (etcdContract γ)`, which is W0's `servesAt γ ep`: `servesAt_addr`) and serves.

Proof sketch: `grpc.CustomCodec(&codec{})` (`codecOk`: the codec's `Marshal`/`Unmarshal` are golang/protobuf's, which call protobuf-go's: `Proto.Marshal.spec`, `Unmarshal.spec`), `Creds` if TLS, `getServerMetrics.spec`, the interceptors (`newLogUnaryInterceptor`, the metrics', `newUnaryInterceptor`, the caller's; the metrics' and `newStreamInterceptor`'s: all `icEtcdOk`/`sicEtcdOk`), `ChainUnaryInterceptor`, `ChainStreamInterceptor`, the size and stream limits (`Grpc`'s option specs), `grpc.NewServer` (`srvBuild`), and each `Register*Server` (3h's generated registrations over `Server.RegisterService.spec` and the generated descriptors, `serviceDescAt`) with the service values (`NewQuotaKVServer`, `NewWatchServer` (2b), `NewQuotaLeaseServer`, `NewClusterServer`, `NewAuthServer`, `NewMaintenanceServer`); the health service (`health.NewServer`, `RegisterHealthServer`: in `B.regs`, its contracts `etcdContract`'s health entries, met by `healthRegs_ok`); `serverMetrics.InitializeMetrics(gs)` (`metricsOk_init`). `regsOk`: for each registration, the generated handler decodes (`decOk_call`) and calls the service's method through the chain (`icChain_call`, `icHandler_call`), each interceptor `icEtcdOk`, the method's `HandlerTriple` (this package's specs), giving `unaryOk`; the streams likewise (`streamOk`, 2b's for `Watch`). Integration X: the registrations hold for the run resource `srvGate s gq` (any share: the caller's `Grpc.start` lends `n` of them, from `srvGate_fractional`, and `GracefulStop` gives them back before 2e's `HardStop`); a handler over 2c's request path passes its share to the server method, the others frame it.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Server.lean`: over `isServer` and the contracts (was `grpcCfgOk`, `kvRegs`, `authRegs`, ... with `backendUnderQuota`); every service, auth on and off, a TLS configuration, a caller's interceptor that preserves the contracts.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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
etcd's contracts. -/
def Server.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (tls : Loc) (ic : GoFunc) (gsl : GoSlice) (gvs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ ∗ (⌜tls = null⌝ ∨ Transport.tlsCfgOk tls) ∗ (⌜ic = func.nil⌝ ∨ icEtcdOk ic γ) ∗
      gsl ↦*□ gvs ∗ ([∗list] v ∈ gvs, srvOptAt v id) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server)) (Val #s)) (Val #tls)) (Val #ic)) (Val #gsl))
  {{ (gs : Loc), RET #gs; ∃ B : SrvCfg, srvBuild gs B ∗ ∀ ep (gq : Qp), regsOk B (etcdContract γ ep) (srvGate s gq) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
