/-
`grpc.NewServer(opts...)` (names only; item 4, the server start): the server being built, with the
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.NewServer(opts...)` with options of the kinds `ks` (`grpcSrvOpt`; the slice read-only)
returns a `*grpc.Server` being built (`grpcSrvNew`), with the unary and stream chains the options'
`ChainUnaryInterceptor`/`ChainStreamInterceptor` give, in order, and nothing registered. -/
abbrev grpc.NewServer.spec : Prop :=
  ∀ (sl : GoSlice) (vs : List GoInterface) (ks : List SrvOptKind),
  {{ (sl ↦*□ vs ∗ ⌜List.Forall₂ grpcSrvOpt vs ks⌝ : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.NewServer)) (Val #sl))
  {{ (gs : Loc), RET #gs;
      grpcSrvNew gs (srvOptsUnary ks) (srvOptsStream ks) [] [] [] }}

end spec

end EtcdGrove
end Perennial
