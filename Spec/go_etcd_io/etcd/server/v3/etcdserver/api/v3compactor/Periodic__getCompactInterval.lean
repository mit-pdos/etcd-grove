/-
`v3compactor.Periodic.getCompactInterval` (`periodic.go`). Lean-first (no Rocq counterpart); the spec-first pilot
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

/-- `pc.getCompactInterval()`: `min(period, 1h)`. -/
abbrev v3compactor.Periodic.getCompactInterval.spec : Prop :=
  ∀ (pc : Loc) (pd : time.Duration) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ structFieldRef v3compactor.Periodic go!"period" pc ↦{dq} pd }}
    (App (Val (pc @!! go.GoType.PointerType v3compactor.Periodic.ty @!! go!"getCompactInterval")) (Val #()))
  {{ (d : time.Duration), RET #d; ⌜sint.Z d = min (sint.Z pd) 3600000000000⌝ ∗ structFieldRef v3compactor.Periodic go!"period" pc ↦{dq} pd }}

end spec

end EtcdGrove
end Perennial
