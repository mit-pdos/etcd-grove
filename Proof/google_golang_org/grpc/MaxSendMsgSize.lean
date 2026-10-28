/-
Trust boundary: `grpc.MaxSendMsgSize` (an axiom; see `Spec/google_golang_org/grpc/MaxSendMsgSize.lean`).
-/
module

public import Spec.google_golang_org.grpc.MaxSendMsgSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): a response over the limit is not sent (an error
for the client); the handler ran as without the option. -/
axiom grpc.MaxSendMsgSize.wp_proof : grpc.MaxSendMsgSize.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
