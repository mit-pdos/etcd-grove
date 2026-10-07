/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgProp.v.

One branch of `Step`'s proof: `MsgProp`, a local proposal.

This is **proof structure, not specification**: `Step` has exactly one spec, in
`Spec/raft__Step.lean`, and this module has no `Module Type` and no `Parameter`.
Only `Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import
it; see `notes/decisions.md` (2026-09-17, and 2026-09-18 for why the helpers
moved out of the top-level directory).

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as their second.
* Rocq's `Local Lemma to_pstate_proposed` is `private theorem toPState_proposed`.
* Rocq's `Local Ltac`s are not ported: `wp_load_step` (binds the load of `r.step` in
  function position, as in `MsgVoteResp`), `finish_err err` (`Step`'s tail after
  `r.step(r, m)`: `if err != nil { return err }`, then `return nil`; destructs `err` and
  runs `wp_auto`), `recv_elem` (`∀ m' ∈ recv, m' = a` for `recv` `[]` or `[a]`), and
  `finish_drop` (a dropped proposal: the state is unchanged, `Step.refl`, and `err` is
  `ErrProposalDropped`'s value).
-/
import EtcdGrove.Raft.ElectionProof.Proof.raft__Step.Base

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

namespace StepProof

/-- `proposed` (`Spec/stepLeader.lean`) is `Step.propose`'s state: the log grows by the
batch stamped at the leader's term and the indices after the last one, and the
self-acknowledgement at the new last index is queued. (Checked 2026-10-02: the physical
definition and the rule agree; nothing needed changing.) -/
private theorem toPState_proposed (id : w64) (s : NState) (ents : List raftpb.Entry) :
    toPState (proposed id s ents) =
    psendMsgs
      (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))
      [pselfAck id
         (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))] := by
  -- PORT: proof
  sorry

/-- `MsgProp`: a local message (`Term = 0`), so the term preamble is skipped and the
type switch's default arm runs `r.step(r, m)`:

- `stepFollower` forwards it to the leader (`Step.propForward`), or, with no leader
  known, drops it (`Step.refl`, `ErrProposalDropped`). `send` holds the entries
  read-only, so the batch is made persistent first;
- `stepCandidate` drops it;
- `stepLeader` appends it (`Step.propose`) and broadcasts (`Step.sendApps`), or drops it
  when `appendEntry` refuses the batch.

`recv` is the proposal itself when it is forwarded, and nothing otherwise. `LeadOk`
(`Protocol/Model.lean`, from `ownRaftGhost`) is what makes the follower's forwarding
`send` not self-addressed. -/
theorem wp_Step_MsgProp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgProp →
    m.Term' = W64 0 →
    (m.From' = W64 0 ∨ m.From' = id) →
    ents ≠ [] →
    (∀ e ∈ ents, e.Type' = EntryNormal) →
    (ents.length : Int) < 2^61 →
    (s.role = .follower → s.lead ≠ id) →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "Hents" ∷ m.Entries' ↦* ents ∗
        "Hcap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- Either one step from `s` consuming at most the proposal (forwarded or
        -- dropped), or -- appended at the leader -- the `Step.propose` state's premises
        -- and one step from that state on (the broadcast), so that `Step` can take
        -- `Step.propose`'s ghost update with the registry
        -- (`ownRaftGhost_step_propose_reg`) and the uniform one for the rest
        -- (2026-10-06).
        "%Hrefines" ∷ ⌜(∃ recv, (∀ m' ∈ recv, m' = absMsg .propose m ents) ∧
              Step cfg id (toPState s) recv (toPState s')) ∨
            (err = interface.nil ∧ (toPState s).role = .leader ∧
             (∀ e ∈ ents, e.Type' = W32 0) ∧
             plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int) < 2 ^ 64 ∧
             Step cfg id
               (psendMsgs (pappend (toPState s)
                   (ents.mapIdx (stamp (toPState s).term (plastIndex (toPState s)))))
                 [pselfAck id (pappend (toPState s)
                   (ents.mapIdx (stamp (toPState s).term (plastIndex (toPState s)))))])
               [] (toPState s'))⌝ ∗
        "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) }} := by
  -- PORT: proof
  sorry

end StepProof

end branches

end EtcdGrove
end Perennial
