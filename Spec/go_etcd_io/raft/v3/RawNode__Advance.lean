/-
## `RawNode.Advance(rd)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** As `node.Advance.spec`'s: `stepsOnAdvance` stepped, each with R2's
`ackOk` (`rawNodeAt_advance.spec`, `raft.Step` with `StepSrc.ack`), leaving none queued. Not async
(`ConfigOk`), so no panic. **Changes.** As `node.Advance`'s; (round 2) over R2's phase token
`rawNodeAt rn γ id k adv` (`ApiCore.lean`), given back with nothing queued.
-/
module

public import Spec.go_etcd_io.raft.v3.Api
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
variable [ctx_sem : context.Assumptions]

/-- `RawNode.Advance`, as `node.Advance` (it cannot stop). -/
def RawNode.Advance.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (st : Driver) (j : Nat) (v : ConfView)
    (rd : go_etcd_io.raft.v3.Ready),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv ∗ nodeDriver rn γ st ∗ readyStor rn none j [] ∗ nodeConf rn γ v ∗
      (match st.lastSnap with
       | none => confSkipped γ st.delivered v.applied st.delivered.length
       | some _ => iprop(True)) }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ RET #(); rawNodeAt rn γ id k false ∗ nodeDriver rn γ { st with lastSnap := none } ∗
      appliedLb rn st.delivered.length ∗
      match st.lastSnap with
      | none => nodeConf rn γ v
      | some s => (∀ a m, confAt γ a m -∗ ⌜uint.nat s.index ≤ a ∧ s.conf.Is m⌝ -∗
            |={⊤}=> nodeConf rn γ ⟨a, m⟩) }}

end spec
end Raft
end EtcdGrove
end Perennial
