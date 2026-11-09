/-
`(*grpc.Server).RegisterService(sd, ss)` (grpc-go, assumed: `server.go`).

Users: the generated `etcdserverpb.Register*Server` (3h), from `v3rpc.Server` (`grpc.go:91-99`).

Why true: `RegisterService` checks that `ss` implements the descriptor's handler type (a fatal log
otherwise: excluded, `ss` is the generated `Register*Server`'s typed argument) and records each
method and stream by its full name `/svc/Method`; it fatals on a duplicate service (each of etcd's
is registered once: the premise).

Changes: from `specs-ref/Spec/google_golang_org/grpc/Server__RegisterService.lean`: the
registrations as (full name, handler, service value).

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The full name of a method of service `svc`. -/
def fullName (svc m : GoString) : GoString := go!"/" ++ svc ++ go!"/" ++ m

/-- `gs.RegisterService(sd, ss)` of a service not registered yet: its methods and streams recorded
with the service value. -/
def Server.RegisterService.spec : Prop :=
  ∀ (gs sd : Loc) (ss : GoInterface) (B : SrvCfg) (svc : GoString) (ms sts : List (GoString × val)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ srvBuild gs B ∗ serviceDescAt sd svc ms sts ∗
      ⌜∀ r ∈ B.regs ++ B.sregs, ∀ m ∈ ms ++ sts, r.1 ≠ fullName svc m.1⌝ }}
    (App (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"RegisterService"))
      (Val #sd)) (Val #ss))
  {{ RET #(); srvBuild gs { B with
        regs := B.regs ++ ms.map (fun m => (fullName svc m.1, m.2, ss)),
        sregs := B.sregs ++ sts.map (fun m => (fullName svc m.1, m.2, ss)) } }}

end spec

end Grpc
end EtcdGrove
end Perennial
