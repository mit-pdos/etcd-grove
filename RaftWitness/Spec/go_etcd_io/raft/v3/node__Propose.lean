/- Lean-first (no Rocq counterpart).

## `node.Propose(ctx, data)` (node.go:469)

A proposal of `data` from any goroutine: `stepWait` of a one-entry `MsgProp`, which `run`
steps as `RawNode.Propose` does. Until stage R7a specified for `context.Background()`.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `propErr cd err`: `nodeErr` (`nil`,
raft's `ErrStopped`, the context's once its `Done()` fired) or the proposal's own result from
`run` (`ErrProposalDropped`, ...; non-`nil`).

**Logically atomic (2026-10-10; persistent since 2026-10-14, stage R).** The full committed
log `rLog γ L` (`Protocol/GhostState.lean`) is the client's: a first proposal of `data`
(`fresh`, with the fresh token `propFresh`) hands in the client's persistent atomic update
`propAu γ data Q` = `□ AU <{ ∃∃ L, rLog γ L }> @ ⊤ ∖ ↑raftN, ∅ <{ ∀∀ e, rLog γ (L ++ [e]) ∗
entDataIs γ e (some data), COMM □ Q L }>`, which `Propose` deposits in the cluster's registry
before the proposal leaves the node (`node_propose_ghost`). It fires -- a linearization point
-- at **every** committed entry holding `data` (a retry or a redelivered proposal may commit
it more than once), on whichever node commits it; the client collects `□ Q L` of each
occurrence with the handle it gets back (`node_collect`), once it sees that entry committed.
A retry (`fresh = false`) needs only `deposited γ data`, which every proposal returns. The
error (`ErrProposalDropped` when no leader is known, ...) says only whether this proposal
reached a leader; the update stays deposited either way.

raft v3.7 (2026-10-16, stage R5): the message is a fresh `*pb.Message` whose one entry holds
`data`'s bytes (D6: `propEntryM data`, the caller's slice frozen, `data_sl ↦*□ data`), on `propc`
(`propP`); the data must be non-empty (D6: an empty proposal would be a leader's own entry).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.Propose.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (data_sl : GoSlice) (data : List w8)
    (Q : List EntryM → IProp GF) (fresh once : Bool)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      nodeCtx ctx cd ∗
      data_sl ↦*□ data ∗
      -- (2026-10-16, stage R5, D6) non-empty data (`node_propose_ghost`)
      ⌜data ≠ []⌝ ∗
      propArg γ.raft data Q fresh once }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok ctx))) (Val #data_sl))
  {{ (err : GoInterface), RET #err; propRes γ.raft data Q fresh once ∗ propErr cd err }}

end spec

end EtcdGrove
end Perennial
