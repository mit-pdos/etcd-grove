/-
## `RawNode.Ready()`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** `readyWithoutAccept` then `acceptReady` (internal: R2's raft
predicates); the batch's facts from raft's log (R3: `nextUnstableEnts`, `nextCommittedEnts`,
`nextUnstableSnapshot`), the messages from `msgs`/`msgsAfterAppend` with their `msgSent` facts
recorded (gated by the enter or the check update), the read states from `readStates`.

**Changes** (from `specs-ref`'s `RawNode__Ready.lean`): the same `readyGot` as the node's (was a
`RawNode`-specific `readyRest` over `ownRawNode`). (Round 2, R2's finding) over R2's phase token:
a `Ready` needs nothing queued (`rawNodeAt ... false`) and leaves the acknowledgements queued
(`... (k+1) true`) until `Advance`; the driver alone did not exclude a second `Ready` (the enter
update gives it back before `Advance`), on which `acceptReady` panics. Proof: `readyWithoutAccept`
(`readyFresh`), R2's `ready_handout.spec`, `acceptReady`.
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

/-- `RawNode.Ready`: what a node's `Ready` receive gives. -/
def RawNode.Ready.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (st : Driver),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k false ∗ nodeDriver rn γ st }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Ready")) (Val #()))
  {{ (rd : go_etcd_io.raft.v3.Ready), RET #rd; rawNodeAt rn γ id (k + 1) true ∗ readyGot rn γ id st rd }}

end spec
end Raft
end EtcdGrove
end Perennial
