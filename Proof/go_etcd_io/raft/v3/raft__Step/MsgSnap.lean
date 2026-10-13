/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap.v.

`Step`'s `MsgSnap` branch (2026-10-02): the term preamble, then the type switch's
default arm `r.step(m)`. Three term cases, each in its own file; this lemma only picks
one:

- `m.Term > r.Term` (`MsgSnap_gt.lean`): the preamble's `becomeFollower(m.Term, m.From)`
  (`Step.higherTerm` at `absSnap`), then `stepFollower`'s `MsgSnap` arm on the
  stepped-down state;
- `m.Term < r.Term` (`MsgSnap_lt.lean`): logged and dropped (`Step.refl`);
- `m.Term = r.Term` (`MsgSnap_eq.lean`): `r.step(m)` by role -- the follower's and the
  candidate's arms adopt the sender and run `handleSnapshot`; a leader is excluded by
  the premise the dispatch derives from `isLeader_unique`.

`handleSnapshot`'s three exits refine `Step.snapStale`, `Step.snapFastfwd` and
`Step.snapRestore` (`step_handle_snap`).

Proof structure, not specification: no `Module Type`, no `Parameter`; only
`Proof/raft__Step.lean`, or another module of this directory, may import it.

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as their second.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.MsgSnap_gt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgSnap_lt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgSnap_eq

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

theorem wp_Step_MsgSnap (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (sv : raftpb.Snapshot) (voters learners : List w64) :
    m.Type' = MsgSnap →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    -- the snapshot's `ConfState` is `cfg`'s voters and learners outside `cfg`, zero-free,
    -- no joint configuration; its index below `2^61` (`Step`'s `"Hsnap"`)
    SnapScope cfg sv voters learners →
    -- protocol facts the dispatch derives from the ghost state: at the current term
    -- the receiver is not a leader (`isLeader_unique`), and a follower's tally is
    -- empty (`FollowerVotesOk`)
    (m.Term' = s.term → s.role ≠ .leader) →
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hsv" ∷ m.Snapshot' ↦□ sv ∗
        "#Hvs" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
        "#Hls" ∷ ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absSnap m sv voters) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hscope Hnl Hvotes
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · exact wp_Step_MsgSnap_gt _P cfg r id s m sv voters learners Hty Hto Hterm Hfnz Hfid Hcfg
      Hwf Hscope Hgt
  · by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · wp_start_folded as ⟨Hphys, -, -, -⟩
      iapply wp_Step_MsgSnap_lt _P cfg r id s m sv voters Hty Hto Hterm Hwf Hlt $$ [$Hpkg $Hphys] HΦ
    · have Hteq : m.Term' = s.term := by word
      exact wp_Step_MsgSnap_eq _P cfg r id s m sv voters learners Hty Hto Hterm Hfnz Hfid Hcfg
        Hwf Hscope Hteq (Hnl Hteq) Hvotes

end StepProof

end branches

end EtcdGrove
end Perennial
