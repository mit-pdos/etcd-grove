/-
`(*grpc.Server).register(sd, ss)` (`server.go`, the model's body; W1, 2026-11-26): what
`RegisterService` calls (the model makes no `HandlerType` check, `server.go:750-753`).
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

/-- `gs.register(sd, ss)` (`RegisterService`'s precondition) on a server being built, for a descriptor `sd` (`grpcDescIs`,
read-only) of a service not registered yet, whose method and stream names are distinct and whose
every stream descriptor sets `ClientStreams` or `ServerStreams` (per-type stage B, B1b: grpc calls
an unflagged stream descriptor's handler directly, without the stream interceptor,
`server.go:1446-1450`, test T10b; `grpcSrvNew`'s invariant), and a service value implementing its
handler type, registers the service: its methods and streams under their full names, with their
handlers and `ss`. -/
abbrev grpc.Server.register.spec : Prop :=
  ∀ (gs sd : Loc) (ss : GoInterface) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × GoFunc × GoInterface)) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
  {{ grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ grpcDescIs (GF := GF) sd sn ht mds sds ∗ ⌜sn ∉ svcs⌝ ∗
      ⌜grpcImplements ss ht⌝ ∗ ⌜(descNames mds sds).Nodup⌝ ∗
      ⌜∀ sd ∈ sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝ }}
    (App (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"register"))
      (Val #sd)) (Val #ss))
  {{ RET #(); grpcSrvNew gs ics sics (svcs ++ [sn]) (regs ++ descRegs sn mds ss)
      (sregs ++ descSRegs sn sds ss) }}

end spec

end EtcdGrove
end Perennial
