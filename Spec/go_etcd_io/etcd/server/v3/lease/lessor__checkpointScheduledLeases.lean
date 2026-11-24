/-
`(*lessor).checkpointScheduledLeases()` (`server/lease/lessor.go:665-689`). Lean-first;
prove-ps2-newlessor3, 2026-11-21.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.checkpointScheduledLeases()` (the expiry loop's): under the write lock, no checkpoint is due
(no checkpointer is installed), so it returns at its first pass. -/
abbrev lease.lessor.checkpointScheduledLeases.spec : Prop :=
  ∀ (lp : Loc) (γl : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"checkpointScheduledLeases")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
