/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgHeartbeatResp.v.

`Step`'s `MsgHeartbeatResp` branch. The three term cases are `wp_Step_Resp_gt`,
`wp_Step_Resp_lt` (shared with `MsgAppResp`) and `wp_Step_MsgHeartbeatResp_eq`, each in
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
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgHeartbeatResp_eq

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

/-- `MsgHeartbeatResp`: dropped if stale, a step-down if from a higher term, otherwise
`r.step(m)` -- at a leader, possibly a `sendAppend`. The empty `Context` (no read-index
requests in scope) keeps `stepLeader` out of the read-only code; `From ≠ id` rules out
`send`'s self-addressed `Panicf`. -/
theorem wp_Step_MsgHeartbeatResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8)
    (Hlrd : s.role = .leader → m.Term' = s.term →
      (RdOk cfg s.rd ∧ s.term ≠ W64 0) ∧ (ctx = [] ∨ 8 ≤ ctx.length) ∧
      (ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
                    ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int))) :
    m.Type' = MsgHeartbeatResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents ∗
        "#Hctx0" ∷ m.Context' ↦*□ ctx }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ c recv, (c = [] ∨ c = ctx) ∧
            (∀ m' ∈ recv, m' = absMsg .heartbeatResp m ents c) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf
  wp_start_folded as ⟨Hphys, -, #Hctx0⟩
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · wp_apply (wp_Step_Resp_gt _P cfg r id s m ents .heartbeatResp (.inr ⟨Hty, rfl⟩) Hto Hterm
        Hgt Hwf) $$ [$Hpkg $Hphys] as %err %s' ⟨Hphys, %Hwf', %Href, %Herr, %Hfr, %Htm⟩
    iapply HΦ $$ %err %s'
    iframe Hphys
    ipureintro
    obtain ⟨recv, Hrecv, Hstep⟩ := Href
    exact ⟨Hwf', ⟨[], recv, .inl rfl, Hrecv, Hstep⟩, Herr, Hfr, Htm⟩
  · by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · wp_apply (wp_Step_Resp_lt _P cfg r id s m ents .heartbeatResp (.inr Hty) Hterm Hlt Hwf)
        $$ [$Hpkg $Hphys] as %err %s' ⟨Hphys, %Hwf', %Href, %Herr, -, %Hfr, %Htm⟩
      iapply HΦ $$ %err %s'
      iframe Hphys
      ipureintro
      obtain ⟨recv, Hrecv, Hstep⟩ := Href
      exact ⟨Hwf', ⟨[], recv, .inl rfl, Hrecv, Hstep⟩, Herr, Hfr, Htm⟩
    · have Hteq : m.Term' = s.term := by word
      wp_apply (wp_Step_MsgHeartbeatResp_eq _P cfg r id s m ents ctx Hlrd Hty Hto Hterm Hteq Hfnz
        Hfid Hcfg Hwf) $$ [$Hpkg $Hphys $Hctx0] as %err %s' ⟨Hphys, %Hwf', %Href, %Herr, %Hfr, %Htm⟩
      iapply HΦ $$ %err %s'
      iframe Hphys
      ipureintro
      obtain ⟨recv, Hrecv, Hstep⟩ := Href
      exact ⟨Hwf', ⟨ctx, recv, .inr rfl, Hrecv, Hstep⟩, Herr, Hfr, Htm⟩

end StepProof

end branches

end EtcdGrove
end Perennial
