/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgApp.v.

`Step`'s `MsgApp` branch: the term preamble, then the type switch's default arm
`r.step(m)`. Three term cases, each in its own file so that they check in parallel;
this lemma only picks one:

- `m.Term > r.Term` (`proof_raft__Step_MsgApp_gt.v`): the preamble's
  `becomeFollower(m.Term, m.From)` (`Step.higherTerm`, which adopts the sender for a
  `fromLeader` type), then `stepFollower`'s arm on the stepped-down state;
- `m.Term < r.Term` (`_lt.v`): with `checkQuorum` and `preVote` off the message is
  logged and dropped (`Step.refl`, nothing received);
- `m.Term = r.Term` (`_eq.v`): `r.step(m)` by role -- the follower's and the
  candidate's arms adopt the sender and run the handler, the leader's does nothing.

Proof structure, not specification: no `Module Type`, no `Parameter`; only
`Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* The statement is the one `Proof/raft__Step.lean` had for this branch before the
  split (Rocq's, with the GUARD on the conflict/commit premise and the follower-votes
  premise); the proof dispatches on the term to the three sub-case lemmas
  (`wp_Step_MsgApp_gt`, `_lt`, `_eq`).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.MsgApp_gt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgApp_lt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgApp_eq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

theorem wp_Step_MsgApp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgApp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    NStateWf s →
    -- protocol facts the dispatch derives from the ghost state (`app_recv_wf`,
    -- `app_no_conflict_below_commit`)
    PlogWf (entryID.mk m.LogTerm' m.Index') ents →
    uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
    -- GUARD (2026-10-02, the dispatch): the protocol fact holds only for a message no
    -- older than the receiver's term; a stale `MsgApp` is dropped by the preamble and
    -- never reaches `maybeAppend`
    (uint.Z s.term ≤ uint.Z m.Term' →
     uint.Z s.logst.committed ≤ uint.Z m.Index' →
     PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents)
       (entryID.mk m.LogTerm' m.Index') →
     plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents = W64 0 ∨
     uint.Z s.logst.committed <
       uint.Z (plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents)) →
    -- ADDED (not in the brief): a follower's vote tally is empty. The follower case
    -- of `m.Term = r.Term` refines `step_app_accept` / `step_heartbeat` etc., whose
    -- `padoptLeader` clears `votes`; the Go code's `r.lead = m.From` does not touch
    -- `r.trk.Votes`, so the two agree only when the tally already is empty.
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents ∗
        "Hcap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .app m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw Hconf Hvotes
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · exact wp_Step_MsgApp_gt _P cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw
      (Hconf (by omega)) Hgt
  · by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · exact wp_Step_MsgApp_lt _P cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw
        Hlt
    · have Hteq : m.Term' = s.term := by word
      exact wp_Step_MsgApp_eq _P cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw
        (Hconf (by omega)) Hteq Hvotes

end StepProof

end branches

end EtcdGrove
end Perennial
