/-
`(*Periodic).getCompactInterval` (`periodic.go`; etcd#18472 makes it return the configured
`interval` when it is non-zero). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `pc.getCompactInterval()` reads `pc.period` and `pc.interval` and returns
`pdCompactInterval period interval`: `interval` when it is non-zero, else `min(period,
time.Hour)`. (Before etcd#18472: always `min(period, time.Hour)`, `pdCompactIntervalOld`; the
two agree when `interval = 0`, `getCompactInterval.spec_implies_old` in the proof file.) -/
abbrev v3compactor.Periodic.getCompactInterval.spec : Prop :=
  ∀ (pc : Loc) (p i : w64) (dq dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ pdPeriodAddr pc ↦{dq} p ∗ pdIntervalAddr pc ↦{dq'} i }}
    (App (Val (pc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"getCompactInterval")) (Val #()))
  {{ RET #(pdCompactInterval p i); pdPeriodAddr pc ↦{dq} p ∗ pdIntervalAddr pc ↦{dq'} i }}

end spec

end EtcdGrove
end Perennial
