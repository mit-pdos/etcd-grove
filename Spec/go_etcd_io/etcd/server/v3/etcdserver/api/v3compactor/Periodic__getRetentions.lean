/-
`v3compactor.Periodic.getRetentions` (`periodic.go`). Lean-first (no Rocq counterpart); the spec-first pilot
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

/-- `pc.getRetentions()`: `period / retry + 1` (`retentionsOf`; `retry` is not `0` from `10ns` on:
`issues/etcd-compactor-periodic-tiny-retention.md`). -/
abbrev v3compactor.Periodic.getRetentions.spec : Prop :=
  ∀ (pc : Loc) (pd : time.Duration) (dq : DFrac),
  10 ≤ sint.Z pd →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ structFieldRef v3compactor.Periodic go!"period" pc ↦{dq} pd }}
    (App (Val (pc @!! go.GoType.PointerType v3compactor.Periodic.ty @!! go!"getRetentions")) (Val #()))
  {{ (n : w64), RET #n; ⌜sint.Z n = retentionsOf (sint.Z pd)⌝ ∗ structFieldRef v3compactor.Periodic go!"period" pc ↦{dq} pd }}

end spec

end EtcdGrove
end Perennial
