/-
## `needStorageApplyMsg(rd)` (internal)

`acceptReady`, `readyWithoutAccept`. Mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

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
variable [ctx_sem : context.Assumptions]

/-- (internal) Whether the `Ready` has committed entries. -/
def needStorageApplyMsg.spec : Prop :=

  ∀ (rd : go_etcd_io.raft.v3.Ready),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (@! go_etcd_io.raft.v3.needStorageApplyMsg)) (Val #rd))
  {{ (b : Bool), RET #b; ⌜b = decide (sint.Z rd.CommittedEntries'.len > 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
