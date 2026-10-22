/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap.v.

`Step`'s `MsgSnap` branch (2026-10-02): the term preamble, then the type switch's
default arm `r.step(m)`. Three term cases, each in its own file; this lemma only picks
one:

- `m.Term > r.Term` (`MsgSnap_gt.lean`): the preamble's `becomeFollower(m.Term, m.From)`
  (`StepC.higherTerm` at `absSnap`), then `stepFollower`'s `MsgSnap` arm on the
  stepped-down state;
- `m.Term < r.Term` (`MsgSnap_lt.lean`): logged and dropped (`StepC.refl`);
- `m.Term = r.Term` (`MsgSnap_eq.lean`): `r.step(m)` by role -- the follower's and the
  candidate's arms adopt the sender and run `handleSnapshot`; a leader is excluded by
  the premise the dispatch derives from `isLeader_unique`.

`handleSnapshot`'s three exits refine `StepC.snapStale`, `StepC.snapFastfwd` and
`StepC.snapRestore` (`step_handle_snap`), and (2026-10-14, stage B8) the dynamic model's
`StepR` rules of the same names, the restore at the configuration the snapshot's `ConfState`
denotes (`stepCDS_handle_snap`, `StepCDS`).

Proof structure, not specification: no `Module Type`, no `Parameter`; only
`Proof/raft__Step.lean`, or another module of this directory, may import it.

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
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

set_option maxHeartbeats 1000000 in
theorem wp_Step_MsgSnap (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (scfg : CSLists) (sv : SnapshotM)
    -- (2026-10-19, D21 M3) not in the no-snapshot mode (`raft.restore`'s premise)
    (Hnsf : s.gh.ns = false) :
    m.Type' = MsgSnap →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    NStateWf s →
    -- the snapshot's `ConfState` well formed, any (joint included), its index below `2^61`
    -- (`Step`'s `"Hsnap"`)
    SnapScopeIf id sv scfg →
    -- (stage R4) the snapshot the message holds, and its `ConfState`'s lists
    sn = some sv →
    scfg = sv.Metadata'.ConfState'.lists →
    -- protocol facts the dispatch derives from the ghost state: at the current term
    -- the receiver is not a leader (`isLeader_unique`), and a follower's tally is
    -- empty (`FollowerVotesOk`)
    (m.Term' = s.term → s.role ≠ .leader) →
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (D22 S-b′3, 2026-10-20) the snapshot certified in the storage's registry
        "#Hcert" ∷ storCert s.logst.storage (snapTrip sv sv.Metadata'.ConfState'.lists) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (c' : CfgM), RET #err;
        "Hphys" ∷ ownRaftPhysCV c' c'.voters r id s' ∗
        -- (2026-10-14, stage B7) the snapshot's configuration after a restore
        "%Hc'" ∷ ⌜c' = c ∨ (c' = snapCfg sv scfg ∧ scfg.Has id)⌝ ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absSnap m sv scfg) ∧
            StepCDS c c' (snapCfg sv scfg) id B (snapId sv) s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        -- (2026-10-19, D21 M3) the no-snapshot mode kept
        "%Hng" ∷ ⌜s'.gh = s.gh⌝ ∗
        -- (2026-10-20, D22 S-c) what is kept of the state, and the term
        "%Hsf" ∷ ⌜SnapStep m s s' ∧ SnapLogStep sv m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hscope Hsn Hscl Hnl Hvotes
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · exact wp_Step_MsgSnap_gt _P _Q c r id s ml m sn ctx rs ents scfg sv Hnsf Hty Hto Hterm Hfnz Hfid
      Hwf Hscope Hsn Hscl Hgt
  · by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · wp_start_folded as ⟨Hphys, Hm, -⟩
      iapply wp_Step_MsgSnap_lt _P _Q c r id s ml m sn ctx rs ents sv scfg Hty Hto Hterm Hwf Hlt $$ [$Hpkg $Hphys $Hm]
      inext
      iintro %err %s' ⟨Hphys, %Hwf', %Href, %Herr, %Hng, %Hsf⟩
      iapply HΦ $$ %err %s' %c
      iframe Hphys
      ipureintro
      exact ⟨Or.inl rfl, Hwf', Href, Herr, Hng, Hsf⟩
    · have Hteq : m.Term' = s.term := by word
      exact wp_Step_MsgSnap_eq _P _Q c r id s ml m sn ctx rs ents scfg sv Hnsf Hty Hto Hterm Hfnz Hfid
        Hwf Hscope Hsn Hscl Hteq (Hnl Hteq) Hvotes

end StepProof

end branches

end EtcdGrove
end Perennial
