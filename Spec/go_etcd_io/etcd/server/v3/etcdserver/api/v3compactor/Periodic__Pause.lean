/-
`v3compactor.Periodic.Pause` (`periodic.go`). Lean-first (no Rocq counterpart); the spec-first pilot
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

/-- `pc.Pause()` sets `paused` under the write lock, and returns. -/
abbrev v3compactor.Periodic.Pause.spec : Prop :=
  ∀ (pc : Loc) (E : CompactEnv GF) (period : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isPeriodic pc E period }}
    (App (Val (pc @!! go.GoType.PointerType v3compactor.Periodic.ty @!! go!"Pause")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
