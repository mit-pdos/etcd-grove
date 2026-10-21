/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote.v.

`Step`'s `MsgPreVote` branch (2026-10-04), combining the three term cases, each in its
own file so that they check in parallel. Proof structure, not specification: no
`Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩` (until the retarget a value and its `Context` slice), passed to the three cases; the
getter specs `PB` (`ElectionLemmas.lean`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVote_gt
public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVote_eq
public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVote_lt

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

/-- `MsgPreVote`: answered with a `MsgPreVoteResp`, whatever the term; the node's own
state never changes (no step-down, no vote recorded). The protocol step is one
`StepC.sendFree`, consuming nothing. -/
theorem wp_Step_MsgPreVote (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    -- from another node (2026-10-10): the answer goes to `m.From`
    m.From' ≠ id →
    NStateWf s →
    (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true) →
    -- (2026-10-17) the requested term within the node's or the ceiling (`NGhost.tc`)
    (uint.Z m.Term' ≤ uint.Z s.term ∨ uint.Z m.Term' ≤ uint.Z s.gh.tc) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the message, as `Step` received it
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id B m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hutd0 Hptc
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · exact wp_Step_MsgPreVote_gt _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Hfid Hgt Hwf Hutd0
      (Hptc.resolve_left (by omega))
  · wp_start_folded as ⟨Hphys, Hm⟩
    by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · iapply wp_Step_MsgPreVote_lt _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Hfid Hlt Hwf
        $$ [$Hpkg $Hphys $Hm] HΦ
    · have Heq : m.Term' = s.term := by word
      iapply wp_Step_MsgPreVote_eq _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Hfid Heq Hwf
        $$ [$Hpkg $Hphys $Hm] HΦ

end StepProof

end branches

end EtcdGrove
end Perennial
