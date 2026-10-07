/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgAppResp_eq.v.

The current-term case of `Step`'s `MsgAppResp` branch, in its own file so that it
checks in parallel with the other term cases -- see `MsgAppResp.lean`, which combines
them. Proof structure, not specification: no `Module Type`, no `Parameter`; only files
in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem`, `wp_load_step`, `ne_ty` are not ported
  (proof-side helpers; the proof porter may write Lean macros or inline them).
-/
import EtcdGrove.Raft.ElectionProof.Proof.raft__Step.resp_lemmas

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

/-- `MsgAppResp` at `m.Term = r.Term`: the preamble does nothing and the type switch's
default arm runs `r.step(m)`. `stepFollower` and `stepCandidate` have no arm for it
(`Step.refl`); `stepLeader` is the replication path, whose `LeaderStepResult` becomes
`Step.appResp`/`Step.commit`/`Step.sendApps` (`leader_appresp_step`). -/
theorem wp_Step_MsgAppResp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgAppResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.Term' = s.term →
    m.From' ≠ W64 0 →
    (m.Reject' = true → m.From' ≠ id) →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .appResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  -- PORT: proof
  sorry

end StepProof

end branches

end EtcdGrove
end Perennial
