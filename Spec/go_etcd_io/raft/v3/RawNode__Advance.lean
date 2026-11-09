/-
## `RawNode.Advance(rd)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** As `node.Advance.spec`'s (`stepsOnAdvance` stepped). Not async
(`ConfigOk`), so no panic. **Changes.** As `node.Advance`'s.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

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

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (st : Driver) (k : Nat) (v : ConfView)
    (rd : go_etcd_io.raft.v3.Ready),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNode rn γ id ∗ nodeDriver rn γ st ∗ readyStor rn none k [] ∗ nodeConf rn γ v ∗
      (match st.lastSnap with
       | none => confSkipped γ st.delivered v.applied st.delivered.length
       | some _ => iprop(True)) }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ RET #(); rawNode rn γ id ∗ nodeDriver rn γ { st with lastSnap := none } ∗
      appliedLb rn st.delivered.length ∗
      match st.lastSnap with
      | none => nodeConf rn γ v
      | some s => ∃ a m, nodeConf rn γ ⟨a, m⟩ ∗ ⌜uint.nat s.index ≤ a ∧ s.conf.Is m⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
