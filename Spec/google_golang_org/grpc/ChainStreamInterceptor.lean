/-
`grpc.ChainStreamInterceptor(ics...)` (names only; item 4, the server start).
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

/-- `grpc.ChainStreamInterceptor(ics...)`, the slice read-only, returns an option that appends `ics`
to the server's stream chain (`.chainStream ics`). -/
abbrev grpc.ChainStreamInterceptor.spec : Prop :=
  ∀ (sl : GoSlice) (ics : List GoFunc),
  {{ (sl ↦*□ ics : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.ChainStreamInterceptor)) (Val #sl))
  {{ (v : GoInterface), RET #v; ⌜grpcSrvOpt v (.chainStream ics)⌝ }}

end spec

end EtcdGrove
end Perennial
