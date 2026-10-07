/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp.v.

`Step`'s `MsgPreVoteResp` branch (2026-10-04), combining the three term cases, each
in its own file so that they check in parallel. Proof structure, not specification: no
`Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
-/
import EtcdGrove.Raft.Proof.raft__Step.MsgPreVoteResp_gt
import EtcdGrove.Raft.Proof.raft__Step.MsgPreVoteResp_eq
import EtcdGrove.Raft.Proof.raft__Step.MsgPreVoteResp_lt

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

/-- `MsgPreVoteResp`: a rejection of a higher term steps the node down
(`Step.higherTerm`); otherwise only a pre-candidate acts on it
(`step_prevoteRespResult`); a stale one is dropped. -/
theorem wp_Step_MsgPreVoteResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgPreVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    uint.Z s.term + 1 < 2 ^ 64 →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .preVoteResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hnw Hcfg Hwf
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · exact wp_Step_MsgPreVoteResp_gt _P cfg r id s m ents Hty Hto Hterm Hgt Hnw Hcfg Hwf
  by_cases Hlt : uint.Z m.Term' < uint.Z s.term
  · exact wp_Step_MsgPreVoteResp_lt _P cfg r id s m ents Hty Hterm Hlt Hwf
  have Heq : m.Term' = s.term := by word
  exact wp_Step_MsgPreVoteResp_eq _P cfg r id s m ents Hty Hto Hterm Heq Hnw Hcfg Hwf

end StepProof

end branches

end EtcdGrove
end Perennial
