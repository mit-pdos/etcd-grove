/-
`RawNode.readyWithoutAccept` (`rawnode.go:141`), Lean-first (2026-10-10): the first half
of `RawNode.Ready`, which `node.go`'s `run` calls on its own, handing the `Ready` to the
application before `acceptReady`.

Lean notes: as `RawNode.Ready.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `rn.readyWithoutAccept()` builds the `Ready` and changes nothing in the node (Go:
"a read-only operation").

Premises as `RawNode.Ready.spec`'s: `Advance` ran since the last accepted `Ready` and the
application appended its entries (in `node.go`: `advancec == nil`).

What the application gets with `rd` (all of `RawNode.Ready.spec`'s postcondition but the
node and the right to append): the committed entries `ce` extending `rs.delivered`, the
entries `es` to append, the messages to send, each `isRaftMsg`, no snapshot and no read
states. The node is `ownRawNodeReady` (`InvRawnodeReady.lean`): the outbox's slice is now
`rd.Messages`, and `acceptReady rd` takes it to `ownRawNode` at the post-`Ready` state. -/
abbrev RawNode.readyWithoutAccept.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
  rs.steps = [] →
  rs.unpersisted = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"readyWithoutAccept"))
      (Val #()))
  {{ (rd : Ready) (ce es : List raftpb.Entry) (ms : List raftpb.Message), RET #rd;
      "Hrn" ∷ ownRawNodeReady γ rn id rs rd ce es ∗
      "#Hce" ∷ rd.CommittedEntries' ↦*□ ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ rd.Entries' ↦*□ es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms ∗
      "Hmsgs_cap" ∷ ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) ∗
      "#Hmsgs_ok" ∷ ([∗list] m ∈ ms, isRaftMsg γ m) ∗
      "%Hsnapz" ∷ ⌜rd.Snapshot' = zero_val raftpb.Snapshot ∧
                   rd.ReadStates' = slice.nil⌝ }}

end spec

end EtcdGrove
end Perennial
