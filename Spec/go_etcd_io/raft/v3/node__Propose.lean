/- Lean-first (no Rocq counterpart).

## `node.Propose(ctx, data)` (node.go:469)

A proposal of `data` from any goroutine: `stepWait` of a one-entry `MsgProp`, which `run`
steps as `RawNode.Propose` does. Until stage R7a specified for `context.Background()`.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `propErr cd err`: `nodeErr` (`nil`,
raft's `ErrStopped`, the context's once its `Done()` fired) or the proposal's own result from
`run` (`ErrProposalDropped`, ...; non-`nil`).

**Logically atomic (2026-10-10; stage R, 2026-10-14; D21 M6, 2026-10-19; 2026-10-21).** The
full committed log `rLog γ L` (`Protocol/GhostState.lean`) is the client's. Before proposing
`data` the client registers its key `k = entKey (W32 0) data` (the entry's type and bytes,
`entKey`, since 2026-10-27; until then the bytes) with a result predicate `Q`
(`node_prop_register`, a ghost step, once per key, with the fresh token `propFresh`), getting
`propIs γ k Q`. Each proposal of `data` then hands in `propIs γ k Q` and an atomic update
`propAu1 γ k Q` = `AU <{ ∃∃ L, rLog γ L }> @ ⊤ ∖ ↑raftN, ∅ <{ ∀∀ e, rLog γ (L ++ [e]) ∗
entDataIs γ e (some k), COMM □ Q L }>`, which `Propose` deposits in `k`'s slot before the proposal
leaves the node
(`node_propose_ghost`), with a ticket that travels with the proposal. It fires -- a linearization
point -- at most once, at a committed entry holding `data` (the ticket is spent where the
proposal is appended), on whichever node commits it; every committed occurrence of `data` gives
`□ Q` of the log before it (`prop_collect`, from `propIs`). `data` may be proposed any number of
times, each proposal with its own update. An empty `data`
(2026-10-27) is a filler (`Filler`: the same entry as a new leader's), which fires the standing
`noopAu` and takes no update: the client hands in `⌜data = []⌝`. The error (`ErrProposalDropped`, ...) says only
whether this proposal reached a leader; the update stays deposited either way. (Until
2026-10-21 the fresh token went with the first proposal, which returned the handle.)

raft v3.7 (2026-10-16, stage R5): the message is a fresh `*pb.Message` whose one entry holds
`data`'s bytes (D6: `propEntryM data`, the caller's slice frozen, `data_sl ↦*□ data`), on `propc`
(`propP`); until 2026-10-27 the data had to be non-empty (D6: an empty proposal would be a
leader's own entry; it now is one, a filler).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
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
    (Q : List EntryM → IProp GF)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      nodeCtx ctx cd ∗
      data_sl ↦*□ data ∗
      -- (2026-10-27) the proposal tracked under its key `entKey (W32 0) data`, or empty data (a
      -- filler, no update; until then `data ≠ []` was required)
      (⌜data = []⌝ ∨ propArg γ.raft (entKey (W32 0) data) Q) }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok ctx))) (Val #data_sl))
  {{ (err : GoInterface), RET #err; propErr cd err }}

end spec

end EtcdGrove
end Perennial
