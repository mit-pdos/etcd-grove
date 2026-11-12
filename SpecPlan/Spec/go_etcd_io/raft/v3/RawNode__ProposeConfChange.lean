/-
## `RawNode.ProposeConfChange(cc)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** As `node.ProposeConfChange.spec`'s. **Changes.** Unchanged.

**Size premise (integration I2).** `c.wireBound < Proto.marshalMax` (`2^48`: a context under about
`2^47` bytes) is `MarshalConfChange`'s (3h: protobuf-go fails to marshal a larger message; the old
spec had no premise, false of protobuf-go). True of every real change; a client-facing premise until
the user chooses otherwise (3h's open question 3: or a workload premise like grpc's `msgsFit`).
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

/-- `RawNode.ProposeConfChange`. -/
def RawNode.ProposeConfChange.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (cc : GoInterface) (dq : DFrac) (c : ConfChangeI),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv ∗ confChangePts cc dq c ∗ ⌜c.wireBound < Proto.marshalMax⌝ ∗ (□?γ.dup AU <{ ∃∃ (ops : List LogEntry), committedOps γ ops }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (t : w64) (bs : List w8), ⌜decodeConfChange c.entryType bs = some c⌝ ∗
            committedOps γ (ops ++ opsOf [⟨t, c.entryType, bs⟩]), COMM True }>) }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"ProposeConfChange")) (Val #cc))
  {{ (err : GoInterface), RET #err; rawNodeAt rn γ id k adv ∗ confChangePts cc dq c ∗
      (⌜err = interface.nil⌝ ∨ errIs go_etcd_io.raft.v3.ErrProposalDropped err) }}

end spec
end Raft
end EtcdGrove
end Perennial
