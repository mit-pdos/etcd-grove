/-
`(*grpc.Server).Serve(lis)`'s trusted model (`TrustedCode/google_golang_org/grpc.lean`,
`model.Serve`; per-type stage B, B1a, 2026-11-11; Scope r5 §2.2): its spec over the new vocabulary.
B1b makes the model `Server.Serve.impl` and this the spec of `Server.Serve` (with `grpcServeTok`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcRun

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

/-- `gs.Serve(lis)`, with the right to serve `gs` on `lis` as the server `γ` (`grpc.start`'s),
returns an error if it returns. Every call it accepts runs on a goroutine of its own, the handler
meeting the registration its client deposited (the model's `runCall`). -/
abbrev grpc.model.Serve.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface) (γ : GName),
  {{ grpcServeTok (GF := GF) gs lis γ }}
    (App (App (Val google_golang_org.grpc.model.Serve) (Val #gs)) (Val #lis))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
