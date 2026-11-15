/-
## `DefaultLogger.EnableDebug` (`logger.go`)

Sets a flag of a logger not yet shared (`defaultLoggerOwn`; tests and examples set it before use).
**Changes.** New (round 1).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Sets a flag. -/
def DefaultLogger.EnableDebug.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ defaultLoggerOwn l }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.DefaultLogger.ty @!! go!"EnableDebug")) (Val #()))
  {{ RET #(); defaultLoggerOwn l }}

end spec
end Raft
end EtcdGrove
end Perennial
