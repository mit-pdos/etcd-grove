/-
`v3compactor.newRevision` (`revision.go`; etcd#18472 adds the argument `interval`, defaulting
to 5 minutes). Lean-first (no Rocq counterpart).
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
/-- `newRevision(lg, clock, retention, interval, rg, c)` returns a revision compactor
(`isRevision`) holding its arguments, with the wait `rvInterval interval`: `interval`, or
`5 * time.Minute` if it is `0`. -/
abbrev v3compactor.newRevision.spec : Prop :=
  ∀ (lg : Loc) (clk : GoInterface) (retention interval : w64) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ context.isClosedchanInit }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision)) (Val #lg)) (Val #clk)) (Val #retention))
      (Val #interval)) (Val #rg)) (Val #c))
  {{ (rc : Loc), RET #rc; isRevision rc ⟨lg, clk, retention, rvInterval interval, rg, c⟩ }}

end spec

end EtcdGrove
end Perennial
