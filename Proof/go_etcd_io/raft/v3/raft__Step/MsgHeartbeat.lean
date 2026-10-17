/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgHeartbeat.v.

`Step`'s `MsgHeartbeat` branch: the term preamble, then the type switch's default arm
`r.step(m)`. Three term cases, each in its own file so that they check in parallel;
this lemma only picks one:

- `m.Term > r.Term` (`proof_raft__Step_MsgHeartbeat_gt.v`): the preamble's
  `becomeFollower(m.Term, m.From)` (`StepC.higherTerm`, which adopts the sender for a
  `fromLeader` type), then `stepFollower`'s arm on the stepped-down state;
- `m.Term < r.Term` (`_lt.v`): with `checkQuorum` and `preVote` off the message is
  logged and dropped (`StepC.refl`, nothing received);
- `m.Term = r.Term` (`_eq.v`): `r.step(m)` by role -- the follower's and the
  candidate's arms adopt the sender and run the handler, the leader's does nothing.

Proof structure, not specification: no `Module Type`, no `Parameter`; only
`Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* The statement is the one `Proof/raft__Step.lean` had for this branch before the
  split (Rocq's, with the GUARD on the conflict/commit premise and the follower-votes
  premise); the proof dispatches on the term to the three sub-case lemmas
  (`wp_Step_MsgHeartbeat_gt`, `_lt`, `_eq`).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.MsgHeartbeat_gt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgHeartbeat_lt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgHeartbeat_eq

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

set_option maxHeartbeats 1000000 in
theorem wp_Step_MsgHeartbeat (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) :
    m.Type' = MsgHeartbeat →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    NStateWf s →
    -- (until raft#140 the protocol fact `heartbeat_commit_le_last`, under a GUARD: `m.Commit ≤
    -- lastIndex()` for a message no older than the receiver's term; no longer needed)
    -- ADDED (not in the brief): a follower's vote tally is empty (see `MsgApp`)
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .heartbeat m ents ctx) ∧
            StepCD c id m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hvotes
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · exact wp_Step_MsgHeartbeat_gt _P _Q c r id s ml m sn ctx rs ents Hty Hto Hterm Hfnz Hfid Hwf
      Hgt
  · by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · exact wp_Step_MsgHeartbeat_lt _P _Q c r id s ml m sn ctx rs ents Hty Hto Hterm Hfnz Hfid Hwf Hlt
    · have Hteq : m.Term' = s.term := by word
      exact wp_Step_MsgHeartbeat_eq _P _Q c r id s ml m sn ctx rs ents Hty Hto Hterm Hfnz Hfid Hwf
        Hteq Hvotes

end StepProof

end branches

end EtcdGrove
end Perennial
