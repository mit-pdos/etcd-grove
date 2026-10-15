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

/-- `rn.readyWithoutAccept()` builds the `Ready` and changes nothing in the node (Go:
"a read-only operation").

Premises as `RawNode.Ready.spec`'s: `Advance` ran since the last accepted `Ready` and the
application appended its entries (in `node.go`: `advancec == nil`).

What the application gets with `rd` (all of `RawNode.Ready.spec`'s postcondition but the
node and the right to append): the committed entries `ce` extending `rs.delivered`, the
entries `es` to append, the messages to send, each `isRaftMsg`, no snapshot, and (since
2026-10-13) the read states `sts`: `rd.ReadStates` read-only, each `ReadState`
`readStateOk` -- its context a proposed slice whose read was created knowing a committed
log of length at most its index (`readOk`). The slice is read-only because the node
keeps it until `acceptReady` (which sets `r.readStates` to `nil`). The node is `ownRawNodeReady` (`InvRawnodeReady.lean`): the outbox's slice is now
`rd.Messages`, and `acceptReady rd` takes it to `ownRawNode` at the post-`Ready` state.

Since 2026-10-10 also:
- `Hmsgs_term`: every message handed out is of a term at most the node's (`rs.term`), so
  a receiver knows a message's term is at most its sender's (pre-vote is off,
  `ownRawNode`'s scope);
- `Habandon`: the `Ready` may be dropped instead of accepted (`node.go`'s `select` takes
  another case): with the messages given back, the node is whole again, at `rs` with the
  lower bounds raised to what the `Ready` held (`ownRawNodeReady_abandon`). -/
abbrev RawNode.readyWithoutAccept.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
  rs.steps = [] →
  rs.unpersisted = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"readyWithoutAccept"))
      (Val #()))
  {{ (rd : Ready) (ce es : List raftpb.Entry) (ms : List raftpb.Message)
      (sts : List ReadState), RET #rd;
      "Hrn" ∷ ownRawNodeReady γ rn id rs rd ce es ms ∗
      "#Hce" ∷ rd.CommittedEntries' ↦*□ ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ rd.Entries' ↦*□ es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms ∗
      "Hmsgs_cap" ∷ ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) ∗
      "#Hmsgs_ok" ∷ ([∗list] m ∈ ms, isRaftMsg γ m) ∗
      "%Hmsgs_term" ∷ ⌜∀ m ∈ ms, uint.Z m.Term' ≤ uint.Z rs.term⌝ ∗
      "Habandon" ∷ (rd.Messages' ↦* ms -∗
                    ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) -∗
                    ownRawNodeReady γ rn id rs rd ce es ms -∗
                    ∃ (n : Nat) (u : Bool) (c : w64),
                      ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧
                       (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
                         uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
                      ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c }) ∗
      "%Hsnapz" ∷ ⌜rd.Snapshot' = zero_val raftpb.Snapshot⌝ ∗
      -- the read states (2026-10-13)
      "#Hrs" ∷ rd.ReadStates' ↦*□ sts ∗
      "#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateOk γ st) }}

end spec

end EtcdGrove
end Perennial
