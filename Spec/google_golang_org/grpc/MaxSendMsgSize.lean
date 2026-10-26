/-
`grpc.MaxSendMsgSize(n)` (names only; item 4, the server start).
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

/-- `grpc.MaxSendMsgSize(n)` returns a neutral option. -/
abbrev grpc.MaxSendMsgSize.spec : Prop :=
  ∀ (n : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.MaxSendMsgSize)) (Val #n))
  {{ (v : GoInterface), RET #v; ⌜grpcSrvOpt v .neutral⌝ }}

end spec

end EtcdGrove
end Perennial
