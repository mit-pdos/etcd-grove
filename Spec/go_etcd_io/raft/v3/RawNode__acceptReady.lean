/-
## `RawNode.acceptReady(rd)` (internal)

**Users.** `RawNode.Ready` (`rawnode.go:133`) and `node.run` (`node.go:435-436`, right after the send on
`readyc`, at which `ready_handout` handed `rd` out). Snippet: `ready.go`.

**Proof sketch.** The previous `Ready`'s acknowledgements were stepped (`ready_handout` took a fresh
`Ready` computed with none queued), so no panic. `prevSoftSt`, `prevHardSt` move to `rd`'s;
`readStates`, `msgs`, `msgsAfterAppend` cleared (handed out); the acknowledgements queued in
`stepsOnAdvance` (released at `Advance` as `ackOk` by `rawNodeAt_advance`): the self-addressed
responses of `msgsAfterAppend`,
`newStorageAppendRespMsg` (the batch's last entry and snapshot, if any: `needStorageAppendRespMsg`),
`newStorageApplyRespMsg` (the committed entries, if any), each over the opened struct; the log's
`acceptUnstable` and `acceptApplying` (R3). `traceReady` (a no-op).

**Changes** (from `specs-ref`'s `RawNode__acceptReady.lean`): over the `RawNode`'s phases (was the
`Ready`'s record `rof` and the receipt handshake).

**Margin.** A `Ready` not handed out cannot be accepted here (no caller does).
-/
module

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

/-- (internal) Accepts the `Ready` handed out: the next phase, its acknowledgements queued. -/
def RawNode.acceptReady.spec : Prop :=
  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (rd : go_etcd_io.raft.v3.Ready),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ readyHanded rn γ id k rd }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"acceptReady")) (Val #rd))
  {{ RET #(); rawNodeAt rn γ id (k + 1) true }}

end spec
end Raft
end EtcdGrove
end Perennial
