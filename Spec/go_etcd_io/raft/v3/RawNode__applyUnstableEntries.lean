/-
## `RawNode.applyUnstableEntries()` (internal)

`readyWithoutAccept`, `acceptReady`, `HasReady`. Mirrors the code: `!asyncStorageWrites`, which
is off (`ConfigOk`). **Changes.** New (no old spec).
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) `true`: synchronous storage writes. -/
def RawNode.applyUnstableEntries.spec : Prop :=
  ∀ (rn : Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"asyncStorageWrites" rn)
        false dq }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"applyUnstableEntries")) (Val #()))
  {{ RET #true; typedPointsto (structFieldRef go_etcd_io.raft.v3.RawNode go!"asyncStorageWrites" rn)
        false dq }}

end spec
end Raft
end EtcdGrove
end Perennial
