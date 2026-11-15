/-
## `RawNode.Campaign()`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** `raft.Step` of a local message (R2), which returns `nil` for it.
**Changes.** Unchanged.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
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
variable [ctx_sem : context.Assumptions]

/-- `RawNode.Campaign`. -/
def RawNode.Campaign.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Campaign")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ rawNodeAt rn γ id k adv }}

end spec
end Raft
end EtcdGrove
end Perennial
