/-
## `DefaultLogger.Info` (`logger.go`)

The package's default logger, through Go's `log.Logger` (Perennial's `log` model). Prints (a debug line only when enabled) and returns.
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

/-- Logs. -/
def DefaultLogger.Info.spec : Prop :=
  ∀ (l : Loc) (v : GoSlice) (vs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ defaultLoggerOk l ∗ ownSlice v vs dq }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.DefaultLogger.ty @!! go!"Info")) (Val #v))
  {{ RET #(); ownSlice v vs dq }}

end spec
end Raft
end EtcdGrove
end Perennial
