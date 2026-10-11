/- Port of election_proof/spec_RawNode__Propose.v (857d09190).

## `RawNode.Propose` (rawnode.go:90), the client's entry point

`Propose(data)` is one call: `rn.raft.Step(pb.Message{Type: MsgProp, From: rn.raft.id,
Entries: []pb.Entry{{Data: data}}})` -- a one-entry batch whose entry is the zero
`Entry` but for `Data` (`propEntry data_sl`). Since 2026-10-10 the client's atomic update
for the proposal is deposited before (`prop_deposit`, `Protocol/Facts.lean`): the
client hands in the entry's data record (`entData`: the zero slice, or a proposed slice
whose data was deposited), and gets the error back -- `nil` when appended at a leader or
forwarded to one, `ErrProposalDropped` otherwise. Whatever happens to the proposal, its
update fires when the first entry with its data is committed.

The `RawNode`'s client-facing state `rs` is unchanged (`ownRawNode`, `InvRawnode.lean`):
`Step` of a `MsgProp` keeps what it tracks (`LocalStepOk`), so a proposal between
`Ready` and `Advance` does not stop `Advance`.

Until 2026-10-09 the spec was stated on the node's states (`NStateRel`, `Step`,
`ownRaftGhost`); until 2026-10-10 it took the update itself (a plain wand, registered
only when the node was the leader).

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

/-- See the file header. -/
abbrev RawNode.Propose.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (data_sl : GoSlice) (data : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "#Hdata" ∷ data_sl ↦*□ data ∗
      "#Hent" ∷ entData γ (propEntry data_sl) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Propose")) (Val #data_sl))
  {{ (err : GoInterface), RET #err;
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) }}

end spec

end EtcdGrove
end Perennial
