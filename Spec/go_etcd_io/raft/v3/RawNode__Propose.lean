/-
## `RawNode.Propose(data)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** As `node.Propose.spec`'s, synchronously. **Changes.** As `node.Propose`'s.
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

/-- `RawNode.Propose`: the update as `node.Propose`'s; the error `nil` or `ErrProposalDropped`. -/
def RawNode.Propose.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (data_sl : GoSlice) (data : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNode rn γ id ∗ ownSlice data_sl data DFrac.discard ∗ (□?γ.dup AU <{ ∃∃ (ops : List LogEntry), committedOps γ ops }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (t : w64), committedOps γ (ops ++ opsOf [⟨t, EntryNormal, data⟩]), COMM True }>) }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Propose")) (Val #data_sl))
  {{ (err : GoInterface), RET #err; rawNode rn γ id ∗
      (⌜err = interface.nil⌝ ∨ errIs go_etcd_io.raft.v3.ErrProposalDropped err) }}

end spec
end Raft
end EtcdGrove
end Perennial
