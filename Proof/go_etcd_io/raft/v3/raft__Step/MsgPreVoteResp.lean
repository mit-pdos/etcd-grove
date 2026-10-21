/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp.v.

`Step`'s `MsgPreVoteResp` branch (2026-10-04), combining the three term cases, each
in its own file so that they check in parallel. Proof structure, not specification: no
`Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, its getters' specs `PB` (`ElectionLemmas.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVoteResp_gt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVoteResp_eq
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgPreVoteResp_lt

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

/-- `MsgPreVoteResp`: a rejection of a higher term steps the node down
(`StepC.higherTerm`); otherwise only a pre-candidate acts on it
(`stepC_prevoteRespResult`); a stale one is dropped. -/
theorem wp_Step_MsgPreVoteResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- a pre-candidate's term does not wrap (a won pre-vote campaigns)
    (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .preVoteResp m ents) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hnw Hwf
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · exact wp_Step_MsgPreVoteResp_gt _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Hgt Hnw Hwf
  by_cases Hlt : uint.Z m.Term' < uint.Z s.term
  · exact wp_Step_MsgPreVoteResp_lt _P PB c r id s ml m ents sn ctx rs Hty Hterm Hlt Hwf
  have Heq : m.Term' = s.term := by word
  exact wp_Step_MsgPreVoteResp_eq _P PB c r id s ml m ents sn ctx rs Hty Hto Hterm Heq Hnw Hwf

end StepProof

end branches

end EtcdGrove
end Perennial
