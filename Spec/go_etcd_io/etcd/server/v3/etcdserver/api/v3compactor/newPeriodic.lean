/-
`v3compactor.newPeriodic` (`periodic.go`). Lean-first (no Rocq counterpart); the spec-first pilot
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

/-- `newPeriodic(lg, clock, h, rg, c)`: a periodic compactor of period `h` (at least `10ns`) over the
real clock, the revision getter and the compactable, whose `Compact` takes C1's periodic permit;
with the run token. -/
abbrev v3compactor.newPeriodic.spec : Prop :=
  ∀ (lg : Loc) (clk : GoInterface) (h : time.Duration) (E : CompactEnv GF),
  10 ≤ sint.Z h →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ ⌜lg ≠ null⌝ ∗ clockwork.clockOk clockwork.realClock clk ∗
      revGetterOk E.γi E.rg ∗ compactableOk E.c (perPermit E.γi (periodK (sint.Z h))) E.R }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic)) (Val #lg)) (Val #clk)) (Val #h)) (Val #E.rg)) (Val #E.c))
  {{ (pc : Loc), RET #pc; isPeriodic pc E (sint.Z h) ∗ periodicRunTok pc }}

end spec

end EtcdGrove
end Perennial
