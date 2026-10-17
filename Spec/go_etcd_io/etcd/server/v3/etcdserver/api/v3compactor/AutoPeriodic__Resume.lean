/-
`v3compactor.AutoPeriodic.Resume` (`autoperiodic.go`, etcd#22095: it clears `paused` under the mutex).
Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Defs.lean`.
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

/-- `ac.Resume()` on an auto-periodic compactor returns (it clears `paused` under the mutex; the flag's value is not
in the spec: `Run` only skips a sample while it is set, which no spec here states). -/
abbrev v3compactor.AutoPeriodic.Resume.spec : Prop :=
  ∀ (ac : Loc) (P : APParams),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isAutoPeriodic ac P }}
    (App (Val (ac @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic.ty @!! go!"Resume")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
