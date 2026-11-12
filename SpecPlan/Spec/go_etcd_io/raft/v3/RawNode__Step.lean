/-
## `RawNode.Step(m)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** Not a local message (`msgSent`); a response from an unknown peer is
refused (`ErrStepPeerNotFound`); else `raft.Step` (R2), whose only error is `ErrProposalDropped` for
a forwarded proposal. **Changes.** As `node.Step`'s.

**Received messages own their entries' capacity (integration I2, the coordinator's decision).** The
message is `msgRecv` (`msgPts` at `own 1` with its `Entries` slice's spare capacity): raft's
`unstable` may adopt a `MsgApp`'s slice and append into it. rafthttp's decoders deliver fresh
slices (protobuf's unmarshalling; requested of 2f's `recvd` and 2a's `Unmarshal`/`Clone`); an
in-process transport must `proto.Clone` a message another node sent before stepping it
(`nonissues/raft-msgapp-inprocess-aliasing.md`; snippet `ReqDeliver`). Alternative (open for the
user): the fork clips the slice in `logSliceFromMsgApp`, and this premise goes back to `msgPts`.
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

/-- `RawNode.Step` of a received message. -/
def RawNode.Step.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv ∗ msgRecv ml m ∗ msgSent γ m ∗ msgCredit γ m ∗
      ⌜m.to = id⌝ }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface), RET #err; rawNodeAt rn γ id k adv ∗
      (⌜err = interface.nil⌝ ∨ errIs go_etcd_io.raft.v3.ErrStepPeerNotFound err ∨
        errIs go_etcd_io.raft.v3.ErrProposalDropped err) }}

end spec
end Raft
end EtcdGrove
end Perennial
