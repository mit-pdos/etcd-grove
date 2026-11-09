/-
## `RawNode.readyWithoutAccept()` (internal)

**Users.** `RawNode.Ready` (`rawnode.go:132`) and `node.run` (`node.go:363`, at each loop with
`HasReady()` true and no `Advance` due). Snippet: `ready.go` (`ReqReadyFresh`, `ReqReadyStale`).

**Proof sketch.** Reads the log (R3: `nextUnstableEnts`, `nextCommittedEnts(true)`,
`hasNextUnstableSnapshot`/`nextUnstableSnapshot`), `msgs`, the soft and hard state against the
`RawNode`'s previous ones (`SoftState.equal`, `isHardStateEqual`), `readStates`, `MustSync`, and
appends the `msgsAfterAppend` not addressed to the node itself (synchronous writes: `ConfigOk`).
Nothing changes: the result is the `Ready` of the current state (`readyFresh`), its slices sharing
raft's arrays (the core keeps them until `ready_handout`).

**Changes** (from `specs-ref`'s `RawNode__readyWithoutAccept.lean`): over the `RawNode`'s phases
(was `ownRawNode` with `RNState`'s lower bounds `outlb`/`unst`/`clb`).

**Margin.** The `Ready`'s contents are stated by `ready_handout` (R1's `readyGot`), not here.
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

/-- (internal) The `Ready` of the `RawNode`'s current state. -/
def RawNode.readyWithoutAccept.spec : Prop :=
  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"readyWithoutAccept")) (Val #()))
  {{ (rd : go_etcd_io.raft.v3.Ready), RET #rd; readyFresh rn γ id k adv rd }}

end spec
end Raft
end EtcdGrove
end Perennial
