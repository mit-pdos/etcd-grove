/-
**grpc's health server** (split out of `InvGrpcServer.lean`, 2026-11-25, `notes/phase7-endstate.md`
§4): `grpcHealthSrv hs`, persistent, axiomatized: grpc's `*health.Server` `hs`
(`health.NewServer()`), whose `SetServingStatus` is safe from any goroutine. The specs of
`health.NewServer`, `Server.SetServingStatus` and `grpc_health_v1.RegisterHealthServer`
(`Spec/google_golang_org/grpc/health/`) are trust-boundary axioms; this file is their vocabulary.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GooseLang.Lang

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **grpc's health server `hs`** (persistent; see the file header). -/
axiom grpcHealthSrv {GF : BundledGFunctors} [GooseExts] (hs : Loc) : IProp GF

axiom grpcHealthSrv_persistent {GF : BundledGFunctors} [GooseExts] (hs : Loc) :
  Persistent (grpcHealthSrv (GF := GF) hs)

attribute [instance] grpcHealthSrv_persistent

end EtcdGrove
end Perennial
