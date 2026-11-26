/-
`grpcsync.NewEvent()` (grpc's `internal/grpcsync/event.go`, with its body; W1, 2026-11-26): the
server's `quit` and `done` events.
The vocabulary: `Proof/google_golang_org/grpc/InvGrpcServer.lean` (`srvEventIs`).
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

/-- A fresh event (`&Event{c: make(chan struct{})}`): not fired, its channel unbuffered, idle and
owned (`srvEventIs`). -/
abbrev grpcsync.NewEvent.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.internal.grpcsync.NewEvent)) (Val #()))
  {{ (q : Loc), RET #q; srvEventIs q }}

end spec

end EtcdGrove
end Perennial
