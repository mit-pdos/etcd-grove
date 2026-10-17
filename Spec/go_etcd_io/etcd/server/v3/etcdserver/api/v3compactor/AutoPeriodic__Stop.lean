/-
`v3compactor.AutoPeriodic.Stop` (`autoperiodic.go`, etcd#22095: it cancels the compactor's context).
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

/-- `ac.Stop()` cancels `ac`'s context and returns: then the context is done
(`ContextClosed`), so `Run`'s goroutine returns at its next `select` (not stated: liveness). -/
abbrev v3compactor.AutoPeriodic.Stop.spec : Prop :=
  ∀ (ac : Loc) (P : APParams),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isAutoPeriodic ac P }}
    (App (Val (ac @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
