/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgAppResp.v.

`Step`'s `MsgAppResp` branch. The three term cases are `wp_Step_Resp_gt`,
`wp_Step_Resp_lt` (shared with `MsgHeartbeatResp`) and `wp_Step_MsgAppResp_eq`, each in
its own file so they check in parallel; this lemma only picks one. Proof structure, not
specification: no `Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may import
this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Resp_gt
public import Proof.go_etcd_io.raft.v3.raft__Step.Resp_lt
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgAppResp_eq

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
variable [AllG GF]

namespace StepProof

/-- `MsgAppResp`: dropped if stale, a step-down if from a higher term, otherwise
`r.step(m)` -- at a leader, the replication path. `Reject → From ≠ id` is
`stepLeader`'s: a rejecting response from the node itself would make `sendAppend`
address itself. -/
theorem wp_Step_MsgAppResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgAppResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    (m.Reject' = true → m.From' ≠ id) →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .appResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hrej Hcfg Hwf
  wp_start_folded as ⟨Hphys, -⟩
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · wp_apply (wp_Step_Resp_gt _P cfg r id s m ents .appResp (.inl ⟨Hty, rfl⟩) Hto Hterm Hgt Hwf)
      $$ [$Hpkg $Hphys] as %err %s' ⟨Hphys, %Hwf', %Href, %Herr, %Hfr, %Htm⟩
    iapply HΦ $$ %err %s'
    iframe Hphys
    ipureintro
    exact ⟨Hwf', Href, Herr, RespStep.of_fresh (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt), Hfr,
      Htm⟩
  · by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · iapply wp_Step_Resp_lt _P cfg r id s m ents .appResp (.inl Hty) Hterm Hlt Hwf
        $$ [$Hpkg $Hphys] HΦ
    · have Hteq : m.Term' = s.term := by word
      wp_apply (wp_Step_MsgAppResp_eq _P cfg r id s m ents Hty Hto Hterm Hteq Hfnz Hrej Hcfg Hwf)
        $$ [$Hpkg $Hphys] as %err %s' ⟨Hphys, %Hwf', %Href, %Herr, %Hfr, %Htm⟩
      iapply HΦ $$ %err %s'
      iframe Hphys
      ipureintro
      exact ⟨Hwf', Href, Herr, RespStep.of_fresh (by rw [Hty]; w32_ne)
        (Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hteq.symm)), Hfr, Htm⟩

end StepProof

end branches

end EtcdGrove
end Perennial
