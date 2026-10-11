/- Lean-first (no Rocq counterpart).

## `node.Propose(ctx, data)` (node.go:469)

A proposal of `data` from any goroutine: `stepWait` of a one-entry `MsgProp`, which `run`
steps as `RawNode.Propose` does. Specified for `context.Background()`.

**Logically atomic (2026-10-10).** The client log `cLog γ L` (the data of the committed
client entries, first occurrences, `Protocol/GhostState.lean`) is the client's: a first
proposal of `data` (`fresh`, with the fresh token `propFresh`) hands in the client's
atomic update `propAu γ data Q` = `AU <{ ∃∃ L, cLog γ L }> @ ⊤ ∖ ↑raftN, ∅
<{ cLog γ (L ++ [data]), COMM Q L }>`, which `Propose` deposits in the cluster's registry
before the proposal leaves the node (`node_propose_ghost`). It fires -- the
linearization point -- when the first entry with `data` is committed, on whichever node
commits it; the client collects `Q L` with the ticket it gets back (`node_collect`),
once it sees that entry committed. A retry (`fresh = false`) needs only `deposited γ
data`, which every proposal returns. The error (`ErrProposalDropped` when no leader is
known, ...) says only whether this proposal reached a leader; the update stays deposited
either way.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Perennial.Proof.context

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

/-- See the file header. -/
abbrev node.Propose.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (data_sl : GoSlice) (data : List w8)
    (Q : List (List w8) → IProp GF) (fresh : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      data_sl ↦*□ data ∗ propArg γ.raft data Q fresh }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #data_sl))
  {{ (err : GoInterface), RET #err; propRes γ.raft data Q fresh }}

end spec

end EtcdGrove
end Perennial
