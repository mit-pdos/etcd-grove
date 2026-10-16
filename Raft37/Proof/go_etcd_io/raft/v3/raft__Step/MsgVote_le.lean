/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVote_le.v.

One term case of `Step`'s `MsgVote` branch, in its own file so that it checks in
parallel with the other -- see `proof_raft__Step_MsgVote.v` (`MsgVote.lean`), which
combines the two, and `notes/decisions.md` (2026-09-17; 2026-09-18 for why this
directory exists). Proof structure, not specification: no `Module Type`, no
`Parameter`; only `MsgVote.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as its second.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.raft__Step.MsgVote_lt
public import Raft37.Proof.go_etcd_io.raft.v3.raft__Step.MsgVote_eq_novote
public import Raft37.Proof.go_etcd_io.raft.v3.raft__Step.MsgVote_eq_voted

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

/-- `MsgVote` with `m.Term ≤ r.Term`: three cases, each in its own file so they check in
parallel; this lemma only picks one. `m.Term < r.Term` drops the message;
`m.Term = r.Term` answers it, and how depends on whether this node has already voted
in the term. -/
theorem wp_Step_MsgVote_le (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `send` stamps the sender's id into `From`, and node ids are nonzero
    m.From' ≠ W64 0 →
    -- this file: the incoming term is not higher, so no step-down
    ¬ (uint.Z s.term < uint.Z m.Term') →
    -- `r.step` matches the role
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the message, as `Step` received it
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- `recv` is whatever this branch consumed -- nothing, or the incoming message
        -- once or twice. Naming its elements rather than the list lets
        -- `raft.Step.wp_proof` discharge the `isMessage` side of `ownRaftGhost_step`
        -- from the single fact it holds about `m`.
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .vote m ents) ∧
            StepCD c id m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hle0 Hwf
  by_cases Hlt : uint.Z m.Term' < uint.Z s.term
  · exact wp_Step_MsgVote_lt _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Hlt Hwf
  · have Heq : m.Term' = s.term := by word
    by_cases Hv0 : s.vote = W64 0
    · exact wp_Step_MsgVote_eq_novote _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Heq Hv0 Hwf
    · exact wp_Step_MsgVote_eq_voted _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hfnz Heq Hv0 Hwf

end StepProof

end branches

end EtcdGrove
end Perennial
