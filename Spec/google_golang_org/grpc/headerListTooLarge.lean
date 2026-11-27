/-
`headerListTooLarge(fields)` (the grpc model's `model_wire.go`, F1 of `notes/phase7-plan.md` §0a):
whether the header list is over the receiver's 16 MiB limit, as HTTP/2 counts it (`headerListOk`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcWire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header: `false` exactly when the list is within the limit. -/
abbrev grpc.headerListTooLarge.spec : Prop :=
  ∀ (s : GoSlice) (hs : List google_golang_org.grpc.headerField) (dq : DFrac),
  {{ (s ↦*{dq} hs : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.headerListTooLarge)) (Val #s))
  {{ (r : Bool), RET #r; s ↦*{dq} hs ∗ ⌜r = false ↔ headerListOk (hfPairs hs)⌝ }}

end spec

end EtcdGrove
end Perennial
