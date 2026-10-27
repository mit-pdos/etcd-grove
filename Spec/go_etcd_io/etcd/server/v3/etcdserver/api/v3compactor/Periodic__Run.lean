/-
`v3compactor.Periodic.Run` (`periodic.go`). Lean-first (no Rocq counterpart); the spec-first pilot
(`notes/compactor-pilot-plan.md`, phase 1: the specs, written before the proofs).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `pc.Run()`: starts the goroutine that samples the revision every `retry` and compacts, and returns.
The goroutine keeps the run token and `runPre`'s resources, sets the first sample (`firstSample`)
once, and calls `Compact` only at revisions C1's periodic permit allows (`runPre`'s `compactableOk`:
that is what its proof shows). -/
abbrev v3compactor.Periodic.Run.spec : Prop :=
  ∀ (pc : Loc) (E : CompactEnv GF) (period : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isPeriodic pc E period ∗ periodicRunTok pc ∗
      runPre E (perPermit E.RevLb period E.γf) }}
    (App (Val (pc @!! go.GoType.PointerType v3compactor.Periodic.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
