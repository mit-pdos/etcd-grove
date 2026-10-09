/- Port of election_proof/spec_RawNode__Propose.v (857d09190).

## `RawNode.Propose` (rawnode.go:90), the client's entry point

`Propose(data)` is one call: `rn.raft.Step(pb.Message{Type: MsgProp, From: rn.raft.id,
Entries: []pb.Entry{{Data: data}}})` -- a one-entry batch whose entry is the zero
`Entry` but for `Data` (`propEntry data_sl`). So its spec is `Step`'s `MsgProp` arm
(`Spec/raft__Step.lean`) for that batch and one proposal update:

- the client hands in `propAu γ e0 Q` (`Protocol/GhostState.lean`, "The proposal
  registry"): an update of the global committed log that runs when the entry, stamped
  at some `(t, i)`, is committed, with result `Q t i`;
- appended at the leader (the node is the leader and `appendEntry` accepted it), the
  update is registered at the entry's `(term, index)` -- `ps`'s term and the index
  after `ps`'s last -- and the client gets `isProp` and the token `propTok`, which it
  trades for `Q t i` with `prop_collect` once `isCommitted` shows an entry of term `t`
  at `i`;
- otherwise -- forwarded to the leader by a follower (`err = nil`), or dropped
  (`ErrProposalDropped`: no leader known, a candidate, the leader refused it) -- the
  update comes back unrun. A forwarded proposal is not tracked: when the leader appends
  it, the update is not there (the forwarded `MsgProp` carries no ghost state).

The `RawNode` is `ownRawNode` (`InvRawnode.lean`; folded in on 2026-10-06 when the
RawNode branch merged): `Propose` only steps `rn.raft`, so the `RawNode`'s own state
`rs` is unchanged.

`From: rn.raft.id` is why `Step`'s `MsgProp` premise and `send`'s `From` premise admit
`From = id` since 2026-10-06.

Lean notes:
* Rocq's `prop_entry` is `propEntry`.
* As for `raft.Step.spec` (see its Lean notes), the section fixes `hlc :=
  HasLC.hasLC` (`ownRaftGhost` needs `[InvGS GF]`, the heap's invariant instance only
  at `.hasLC`) and has `[AllG GF]`.
* Rocq's `word.add (plast_index ps) (W64 1)` is `plastIndex ps + W64 1`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__Step
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
  ∀ (cfg : GSet w64) (γ : RaftNames)
    (rn : Loc) (id : w64)
    (s : NState) (ps : PState) (rs : RNState)
    (data_sl : GoSlice) (data : List w8) (Q : w64 → w64 → IProp GF),
  -- `Step`'s premises that are not about the message
  γ.reCfg = cfg →
  id ∈ cfg →
  NStateRel s ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode cfg rn id s rs ∗
      "Hghost" ∷ ownRaftGhost γ id ps ∗
      "#Hdata" ∷ data_sl ↦*□ data ∗
      "Hau" ∷ propAu γ (propEntry data_sl) Q }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Propose")) (Val #data_sl))
  {{ (err : GoInterface) (s' : NState) (ps' : PState), RET #err;
      "Hrn" ∷ ownRawNode cfg rn id s' rs ∗
      "Hghost" ∷ ownRaftGhost γ id ps' ∗
      "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
      "%Hrefines" ∷ ⌜∃ recv, Step cfg id ps recv ps'⌝ ∗
      "Hres" ∷ (
        -- appended at the leader: registered at `(ps.term, last + 1)`
        (⌜err = interface.nil ∧ ps.role = .leader⌝ ∗
         ∃ γp, isProp γ ps.term (plastIndex ps + W64 1) γp Q ∗
               propTok γp)
        -- forwarded or dropped: the update back
      ∨ (propAu γ (propEntry data_sl) Q ∗
         (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err))) }}

end spec

end EtcdGrove
end Perennial
