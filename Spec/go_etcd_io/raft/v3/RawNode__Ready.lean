/-
## `RawNode.Ready()`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** `readyWithoutAccept` then `acceptReady` (internal: R2's raft
predicates); the batch's facts from raft's log (R3: `nextUnstableEnts`, `nextCommittedEnts`,
`nextUnstableSnapshot`), the messages from `msgs`/`msgsAfterAppend` with their `msgSent` facts
recorded (gated by the enter or the check update), the read states from `readStates`.

**Changes** (from `specs-ref`'s `RawNode__Ready.lean`): the same `readyGot` as the node's (was a
`RawNode`-specific `readyRest` over `ownRawNode`). **Margin.** A second `Ready` before `Advance`
panics in Go; the spec needs the driver, which only the first batch's enter update gives back.
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

/-- `RawNode.Ready`: what a node's `Ready` receive gives. -/
def RawNode.Ready.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (st : Driver),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNode rn γ id ∗ nodeDriver rn γ st }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Ready")) (Val #()))
  {{ (rd : go_etcd_io.raft.v3.Ready), RET #rd; rawNode rn γ id ∗ readyGot rn γ id st rd }}

end spec
end Raft
end EtcdGrove
end Perennial
