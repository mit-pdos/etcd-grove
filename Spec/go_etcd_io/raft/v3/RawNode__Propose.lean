/- Port of election_proof/spec_RawNode__Propose.v (857d09190).

## `RawNode.Propose` (rawnode.go:90), the client's entry point

`Propose(data)` is one call: `rn.raft.Step(pb.Message{Type: MsgProp, From: rn.raft.id,
Entries: []pb.Entry{{Data: data}}})` -- a one-entry batch whose entry is the zero
`Entry` but for `Data` (`propEntry data_sl`). The client hands in `propAu γ e0 Q`
(`Protocol/GhostState.lean`, "The proposal registry"): an update of the global
committed log that runs when the entry, stamped at some `(t, i)`, is committed, with
result `Q t i`. Either

- the proposal is tracked (`err = nil`): the client gets `isProp γ t i γp Q` and the
  token `propTok γp`, which it trades for `Q t i` with `prop_collect` once
  `isCommitted` shows an entry of term `t` at `i` (the node was the leader and
  appended it at `(t, i)`); or
- the update comes back unrun: forwarded to the leader (`err = nil`; a forwarded
  proposal is not tracked -- the forwarded `MsgProp` carries no ghost state) or dropped
  (`ErrProposalDropped`: no leader known, a candidate, the leader refused it).

The `RawNode`'s client-facing state `rs` is unchanged (`ownRawNode`, `InvRawnode.lean`):
`Step` of a `MsgProp` keeps what it tracks (`LocalStepOk`), so a proposal between
`Ready` and `Advance` does not stop `Advance`.

Until 2026-10-09 the spec was stated on the node's states (`NStateRel`, `Step`,
`ownRaftGhost`) and said where a tracked proposal sits (`(ps.term, plastIndex ps + 1)`,
at a leader); a client needs only the `isProp`, whatever its `(t, i)`.

`From: rn.raft.id` is why `Step`'s `MsgProp` premise and `send`'s `From` premise admit
`From = id` since 2026-10-06.

Lean notes:
* Rocq's `prop_entry` is `propEntry`.
* As for `raft.Step.spec` (see its Lean notes), the section fixes `hlc :=
  HasLC.hasLC` (`ownRawNode` holds `ownRaftGhost`, which needs `[InvGS GF]`, the heap's
  invariant instance only at `.hasLC`) and has `[AllG GF]`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The entry `Propose` builds: `pb.Entry{Data: data}`. -/
def propEntry [FfiSyntax] (data_sl : GoSlice) : raftpb.Entry :=
  { (zero_val raftpb.Entry) with Data' := data_sl }

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- See the file header. -/
abbrev RawNode.Propose.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (data_sl : GoSlice) (data : List w8) (Q : w64 → w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "#Hdata" ∷ data_sl ↦*□ data ∗
      "Hau" ∷ propAu γ (propEntry data_sl) Q }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Propose")) (Val #data_sl))
  {{ (err : GoInterface), RET #err;
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hres" ∷ (
        -- tracked: appended at the leader
        (⌜err = interface.nil⌝ ∗
         ∃ (t : w64) (i : w64) (γp : GName × GName), isProp γ t i γp Q ∗ propTok γp)
        -- forwarded or dropped: the update back
      ∨ (propAu γ (propEntry data_sl) Q ∗
         (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err))) }}

end spec

end EtcdGrove
end Perennial
