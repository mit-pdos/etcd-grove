/-
`grpc.NewServer(opts...)` (the model's body since W1, 2026-11-26; item 4, the server start): the server being built, with the
options' interceptor chains.
The vocabulary: `Proof/google_golang_org/grpc/InvGrpcServer.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.NewServer(opts...)` with options of the kinds `ks` (`grpcSrvOpt`; the slice read-only)
returns a `*grpc.Server` being built (`grpcSrvNew`; W1, 2026-11-26: with grpc's package fact,
`defaultServerOptions` and `globalServerOptions`, which its body reads), with the unary and stream chains the options'
`ChainUnaryInterceptor`/`ChainStreamInterceptor` give, in order, and nothing registered. -/
abbrev grpc.NewServer.spec : Prop :=
  ∀ (sl : GoSlice) (vs : List GoInterface) (ks : List SrvOptKind),
  {{ (isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ sl ↦*□ vs ∗
      ([∗list] v;k ∈ vs;ks, grpcSrvOpt v k) : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.NewServer)) (Val #sl))
  {{ (gs : Loc), RET #gs;
      grpcSrvNew gs (srvOptsUnary ks) (srvOptsStream ks) [] [] [] }}

end spec

end EtcdGrove
end Perennial
