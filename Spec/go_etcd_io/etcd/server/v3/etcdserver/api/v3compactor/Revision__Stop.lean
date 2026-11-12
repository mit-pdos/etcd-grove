/-
`v3compactor.Revision.Stop` (`revision.go`). Lean-first (no Rocq counterpart); the spec-first pilot
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

/-- `rc.Stop()` cancels the compactor's context, and returns. -/
abbrev v3compactor.Revision.Stop.spec : Prop :=
  ∀ (rc : Loc) (E : CompactEnv GF) (ret : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isRevision rc E ret }}
    (App (Val (rc @!! go.GoType.PointerType v3compactor.Revision.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
