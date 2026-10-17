/-
`grpc.CustomCodec(c)` (names only, deprecated in grpc; item 4, the server start): etcd's
`v3rpc.Server` installs its protobuf codec.
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

/-- `grpc.CustomCodec(c)` of a protobuf codec (`grpcProtoCodec`) returns a neutral option. -/
abbrev grpc.CustomCodec.spec : Prop :=
  ∀ (c : GoInterface),
  {{ (⌜grpcProtoCodec c⌝ : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.CustomCodec)) (Val #c))
  {{ (v : GoInterface), RET #v; ⌜grpcSrvOpt v .neutral⌝ }}

end spec

end EtcdGrove
end Perennial
