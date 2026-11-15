/-
## `SoftState.equal(b)` (internal)

`readyWithoutAccept`, `HasReady`. Mirrors the code.
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

/-- (internal) Field equality of two soft states. -/
def SoftState.equal.spec : Prop :=

  ∀ (a b : Loc) (dqa dqb : DFrac) (sa sb : go_etcd_io.raft.v3.SoftState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ a ↦{dqa} sa ∗ b ↦{dqb} sb }}
    (App (Val (a @!! go.GoType.PointerType go_etcd_io.raft.v3.SoftState.ty @!! go!"equal"))
      (Val #b))
  {{ (r : Bool), RET #r; a ↦{dqa} sa ∗ b ↦{dqb} sb ∗
      ⌜r = decide (sa.Lead' = sb.Lead' ∧ sa.RaftState' = sb.RaftState')⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
