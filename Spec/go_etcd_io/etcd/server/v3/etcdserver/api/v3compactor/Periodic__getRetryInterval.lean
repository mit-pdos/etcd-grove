/-
`(*Periodic).getRetryInterval` (`periodic.go`; unchanged by etcd#18472). Lean-first (no Rocq
counterpart).
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

/-- `pc.getRetryInterval()` reads `pc.period` (at any fraction) and returns
`min(period, time.Hour) / retryDivisor` (`pdRetry`). -/
abbrev v3compactor.Periodic.getRetryInterval.spec : Prop :=
  ∀ (pc : Loc) (p : w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ pdPeriodAddr pc ↦{dq} p }}
    (App (Val (pc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"getRetryInterval")) (Val #()))
  {{ RET #(pdRetry p); pdPeriodAddr pc ↦{dq} p }}

end spec

end EtcdGrove
end Perennial
