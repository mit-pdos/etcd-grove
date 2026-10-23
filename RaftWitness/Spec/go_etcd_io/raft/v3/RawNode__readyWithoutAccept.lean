/-
`RawNode.readyWithoutAccept` (`rawnode.go:141`), Lean-first (2026-10-10): the first half
of `RawNode.Ready`, which `node.go`'s `run` calls on its own, handing the `Ready` to the
application before `acceptReady`.

Lean notes: as `RawNode.Ready.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRawnodeReady

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
- `Hmsgs_term`: every message handed out is of a term within the node's term ceiling
  (`rs.tc`; until 2026-10-17, with pre-vote off, at most the node's term `rs.term`), which
  `node.go`'s budget covers;
- `Habandon`: the `Ready` may be dropped instead of accepted (`node.go`'s `select` takes
  another case): with the messages given back, the node is whole again, at `rs` with the
  lower bounds raised to what the `Ready` held (`ownRawNodeReady_abandon`).

raft v3.7 (2026-10-16, stage R5; `notes/decisions.md`, D8): **the messages are handed out** --
`rd.Messages` (a `[]*pb.Message` aliasing `r.msgs`, extended by the `msgsAfterAppend` messages to
others) holds the pointers of `ms : List QMsg`, each message owned at `readyDq` (a
`MsgAppResp`/`MsgVoteResp`/`MsgPreVoteResp` at half: `acceptReady` reads the other half's
`To`; the application gets those read-only, `issues/nonissues/raft-ready-messages-read-after-handout.md`;
every other message whole); `Habandon` takes them back. `Entries`/`CommittedEntries` are
`entsRO` (`[]*pb.Entry`, read-only), the read states `readStatesPts` (their contexts bytes, D6),
`rd.Snapshot` `nil` (was the zero `Snapshot`), and the hard state `hsOpt rd.HardState' h` (new:
the `Ready` hands out `hardState()`'s fresh pointer, or `nil`). -/
abbrev RawNode.readyWithoutAccept.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
  rs.steps = [] →
  rs.unpersisted = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"readyWithoutAccept"))
      (Val #()))
  {{ (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (μh : List WMsg)
      (sts : List ReadStateM) (h : HardStateM), RET #rd;
      "Hrn" ∷ ownRawNodeReady γ rn id rs rd ce es ms false μh ∗
      "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ entsRO rd.Entries' es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms.map QMsg.loc ∗
      "Hmsgs_cap" ∷ ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
      -- (2026-10-16, stage R5, D8) the messages handed out, a response at half
      "Hmsgs_own" ∷ ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) ∗
      "#Hmsgs_ok" ∷ ([∗list] q ∈ ms, isRaftMsg γ q.st) ∗
      -- (2026-10-17; until then at most `rs.term`) within the term ceiling (a granted pre-vote)
      "%Hmsgs_term" ∷ ⌜∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc⌝ ∗
      -- (2026-10-20, witness support) the requests to the witness handed out
      -- (`rd.WitnessMessages`, the queue `r.witnessMsgs`), each legitimately sent
      "Hwms" ∷ ownWQueue rd.WitnessMessages' μh ∗
      "#Hwms_ok" ∷ ([∗list] μ ∈ μh, isMessage γ (wAbs μ)) ∗
      -- (2026-10-20, W4) each from the node, of a term within its ceiling (but a pre-vote), and in
      -- the static mode to the cluster's witness
      "%Hwms_f" ∷ ⌜∀ μ ∈ μh, μ.frm = id ∧ (μ.ty ≠ MsgPreVote → uint.Z μ.term ≤ uint.Z rs.tc) ∧
        (rs.mode = .static → μ.to = γ.reWit)⌝ ∗
      "Habandon" ∷ (rd.Messages' ↦* ms.map QMsg.loc -∗
                    ownSliceCap Loc rd.Messages' (DFrac.own 1) -∗
                    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) -∗
                    ownWQueue rd.WitnessMessages' μh -∗
                    ownRawNodeReady γ rn id rs rd ce es ms false μh -∗
                    ∃ (n : Nat) (u : Bool) (c : w64),
                      ⌜ms.length + μh.length ≤ n ∧ (es ≠ [] → u = true) ∧
                       (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
                         uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
                      ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c }) ∗
      "%Hsnapz" ∷ ⌜rd.Snapshot' = null⌝ ∗
      -- the read states (2026-10-13)
      "#Hrs" ∷ readStatesPts rd.ReadStates' sts ∗
      "#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateOk γ st) ∗
      -- (2026-10-16, stage R5) the hard state: `nil` when unchanged, else `hardState()`'s fresh
      -- read-only one
      "#Hhard" ∷ hsOpt rd.HardState' h }}

end spec

end EtcdGrove
end Perennial
