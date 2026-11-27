/-
`(*grpc.Server).printf(format, a...)` (`server.go`, the model's body; W1, 2026-11-26): records an
event in the server's event log, of which a server being built has none.
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

/-- With no event log (`events` nil): nothing. -/
abbrev grpc.Server.printf.spec : Prop :=
  ∀ (gs : Loc) (fmt : GoString) (a : GoSlice),
  {{ (structFieldRef google_golang_org.grpc.Server go!"events" gs ↦ GoInterface.nil : IProp GF) }}
    (App (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"printf"))
      (Val #fmt)) (Val #a))
  {{ RET #(); structFieldRef google_golang_org.grpc.Server go!"events" gs ↦ GoInterface.nil }}

end spec

end EtcdGrove
end Perennial
