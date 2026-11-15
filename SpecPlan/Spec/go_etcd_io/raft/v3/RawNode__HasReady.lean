/-
## `RawNode.HasReady()`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** Reads raft's state (R2, R3): with nothing stepped since `rd` was
computed in this phase (`readyKept`), `false` means `rd` is still the current state's `Ready`
(R3's "next" sets are monotone between accepts). **Changes.** (Round 2, R2's request) a `false`
answer restores `readyFresh` of a kept `Ready` (`node.run` hands out a `Ready` computed before
other steps); (integration I2, R2's round-1 item 8) and says that `Ready` is empty (`readyEmpty`,
`ApiCore.lean`'s realization item 6), which `ReqReadyStale` needs. **Margin.** A `true` answer says nothing.
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

/-- `RawNode.HasReady`; `false` makes a `Ready` computed earlier in the phase fresh again. -/
def RawNode.HasReady.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (ord : Option go_etcd_io.raft.v3.Ready),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv ∗
      (match ord with | some rd => readyKept rn k rd | none => iprop(True)) }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"HasReady")) (Val #()))
  {{ (b : Bool), RET #b;
      match ord with
      | some rd => if b then rawNodeAt rn γ id k adv
                   else readyFresh rn γ id k adv rd ∗ ⌜readyEmpty rd⌝
      | none => rawNodeAt rn γ id k adv }}

end spec
end Raft
end EtcdGrove
end Perennial
