/-
`grpc.WithNoProxy()` (grpc's `dialoptions.go`; 2026-11-24, `notes/putget-dist-plan.md` §12, finding
F1: etcdstart's `NewClients` passes it, so that no connection of the examples' clients goes through an
HTTP `CONNECT` proxy). Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvDial

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.WithNoProxy()`: a dial option turning grpc's proxy off (`.noProxy`: its closure sets
`useProxy` to `false`). -/
abbrev grpc.WithNoProxy.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithNoProxy)) (Val #()))
  {{ (o : GoInterface), RET #o; grpcDialOptIs o .noProxy }}

end spec

end EtcdGrove
end Perennial
