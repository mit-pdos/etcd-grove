/-
`v3compactor.newAutoPeriodic` (`autoperiodic.go`, etcd#22095: the constructor).
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
variable [package_sem_ctx : context.Assumptions]
/-- `newAutoPeriodic(lg, clock, retention, rg, c, sg, maxBytes)` returns a new auto-periodic
compactor `ac` holding its arguments (`isAutoPeriodic`, with a fresh context of
`context.WithCancel(context.Background())`), not paused. -/
abbrev v3compactor.newAutoPeriodic.spec : Prop :=
  ∀ (P : APParams),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ context.isClosedchanInit }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newAutoPeriodic))
      (Val #P.lg)) (Val #P.clock)) (Val #P.retention)) (Val #P.rg)) (Val #P.c)) (Val #P.sg))
      (Val #P.maxBytes))
  {{ (ac : Loc), RET #ac; isAutoPeriodic ac P }}

end spec

end EtcdGrove
end Perennial
