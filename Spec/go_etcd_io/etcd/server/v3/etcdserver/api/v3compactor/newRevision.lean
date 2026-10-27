/-
`v3compactor.newRevision` (`revision.go`). Lean-first (no Rocq counterpart); the spec-first pilot
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

/-- `newRevision(lg, clock, retention, rg, c)`: a revision compactor keeping `retention` revisions,
whose `Compact` takes C1's revision permit. -/
abbrev v3compactor.newRevision.spec : Prop :=
  ∀ (lg : Loc) (clk : GoInterface) (ret : w64) (E : CompactEnv GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ ⌜lg ≠ null⌝ ∗ clockwork.clockOk clockwork.realClock clk ∗
      revGetterOk E.γi E.rg ∗ compactableOk E.c (revPermit E.γi (sint.Z ret)) E.R }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision)) (Val #lg)) (Val #clk)) (Val #ret)) (Val #E.rg)) (Val #E.c))
  {{ (rc : Loc), RET #rc; isRevision rc E (sint.Z ret) }}

end spec

end EtcdGrove
end Perennial
