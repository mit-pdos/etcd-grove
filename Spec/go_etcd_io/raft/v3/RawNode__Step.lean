/-
## `RawNode.Step(m)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** Not a local message (`msgSent`); a response from an unknown peer is
refused (`ErrStepPeerNotFound`); else `raft.Step` (R2), whose only error is `ErrProposalDropped` for
a forwarded proposal. **Changes.** As `node.Step`'s.
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

/-- `RawNode.Step` of a received message. -/
def RawNode.Step.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv ∗ msgPts ml (DFrac.own 1) m ∗ msgSent γ m ∗ msgCredit γ m ∗
      ⌜m.to = id⌝ }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface), RET #err; rawNodeAt rn γ id k adv ∗
      (⌜err = interface.nil⌝ ∨ errIs go_etcd_io.raft.v3.ErrStepPeerNotFound err ∨
        errIs go_etcd_io.raft.v3.ErrProposalDropped err) }}

end spec
end Raft
end EtcdGrove
end Perennial
