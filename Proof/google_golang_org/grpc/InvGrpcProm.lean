/-
**grpc-prometheus's server metrics** (split out of `InvGrpcServer.lean`, 2026-11-25,
`notes/phase7-endstate.md` §4): `promSrvMetrics m`, persistent, axiomatized: a `*ServerMetrics` `m`
made by `NewServerMetrics` (its counters and histograms, safe from any goroutine), whose
interceptors are transparent. (Its options, `promSrvMetricsOpt`, are defined in
`Proof/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus/Defs.lean`.)
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

/-- **grpc-prometheus's server metrics `m`** (persistent; see the file header). -/
axiom promSrvMetrics {GF : BundledGFunctors} [GooseExts] (m : Loc) : IProp GF

axiom promSrvMetrics_persistent {GF : BundledGFunctors} [GooseExts] (m : Loc) :
  Persistent (promSrvMetrics (GF := GF) m)

attribute [instance] promSrvMetrics_persistent

end EtcdGrove
end Perennial
