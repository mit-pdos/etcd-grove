/-
Port of `election_proof/spec_RawNode__HasReady.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`: `ownRawNode` holds the ghost state (`InvRawnode.lean`)
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `rn.HasReady()` (`rawnode.go:453`): whether `Ready` would hand out anything -- a new
`SoftState`, a new non-empty `HardState`, a snapshot, messages, unstable entries,
committed entries to apply, read states. Read-only. A client may call `Ready` whenever
`Ready`'s premises hold, whatever `HasReady` says; but `false` is pinned (2026-10-10): the
node is then `ownRawNodeIdle` (`InvRawnodeReady.lean`) -- no queued message and no
unstable entry still to be handed out -- which `node.go` needs to accept a `Ready` it
computed earlier and kept (`ownRawNodeIdle_ready`).

Until 2026-10-09 the spec pinned `false` on the node's protocol state (`NState`: the
soft state is the previous one, the hard state empty or the previous one, the outbox
empty, every unstable entry handed out); that went with the previous `SoftState` and
`HardState` from `RNState`, which no client-facing spec states. -/
abbrev RawNode.HasReady.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"HasReady")) (Val #()))
  {{ (b : Bool), RET #b;
      (⌜b = true⌝ ∗ ownRawNode γ rn id rs) ∨ (⌜b = false⌝ ∗ ownRawNodeIdle γ rn id rs) }}

end spec

end EtcdGrove
end Perennial
