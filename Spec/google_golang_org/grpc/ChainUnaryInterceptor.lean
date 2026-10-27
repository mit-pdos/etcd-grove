/-
`grpc.ChainUnaryInterceptor(ics...)` (names only; item 4, the server start).
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

/-- `grpc.ChainUnaryInterceptor(ics...)`, the slice read-only, returns an option that appends `ics`
to the server's unary chain (`.chainUnary ics`). -/
abbrev grpc.ChainUnaryInterceptor.spec : Prop :=
  ∀ (sl : GoSlice) (ics : List GoFunc),
  {{ (sl ↦*□ ics : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.ChainUnaryInterceptor)) (Val #sl))
  {{ (v : GoInterface), RET #v; ⌜grpcSrvOpt v (.chainUnary ics)⌝ }}

end spec

end EtcdGrove
end Perennial
