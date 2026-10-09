/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_Resp_gt.v.

The higher-term case of `Step`'s `MsgAppResp` and `MsgHeartbeatResp` branches, for both
types at once (they take the same path through the preamble and reach no arm of
`stepFollower`), in its own file so that it checks in parallel with the other term
cases -- see `MsgAppResp.lean` and `MsgHeartbeatResp.lean`, which combine them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem`, `ne_ty`, `wp_load_step` are not ported
  (proof-side helpers; the proof porter may write Lean macros or inline them).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas

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

/-- `m.Term > r.Term` for a `MsgAppResp` or `MsgHeartbeatResp`: neither is `fromLeader`,
so the preamble runs `becomeFollower(m.Term, None)`; the type switch then reaches its
default arm, `r.step(m)`, which is `stepFollower` after the step-down, and
`stepFollower` has no arm for either type. One `Step.higherTerm`. -/
theorem wp_Step_Resp_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ty : MsgType) :
    (m.Type' = MsgAppResp ∧ ty = .appResp) ∨
    (m.Type' = MsgHeartbeatResp ∧ ty = .heartbeatResp) →
    m.To' = id →
    m.Term' ≠ W64 0 →
    uint.Z s.term < uint.Z m.Term' →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg ty m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hgt Hwf
  have Hfl : fromLeader ty = false := by
    rcases Hty with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp := by
    rcases Hty with ⟨Ht, _⟩ | ⟨Ht, _⟩
    · exact .inr (.inl Ht)
    · exact .inr (.inr Ht)
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hgt]
  wp_auto
  rcases Hty with ⟨Hty, -⟩ | ⟨Hty, -⟩
  all_goals iterate 6 (try (rw [Hty]; wp_auto))
  all_goals
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    iterate 6 (try (rw [Hty]; wp_auto))
    wp_apply _P.becomeFollower $$ [$Hphys] as %pvs Hphys
    iterate 6 (try (rw [Hty]; wp_auto))
    wp_apply raft.wp_load_step $$ Hphys as Hphys
    rw [show ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).stepfn =
      stepFuncOf .follower from rfl]
    simp only [stepFuncOf]
    wp_apply _P.stepFollower cfg r id { becomeFollower s m.Term' (W64 0) with prvals := pvs }
        m [] (zero_val _) [] (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs1⟩ := followerStepResult_noop _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %({ becomeFollower s m.Term' (W64 0) with prvals := pvs })
    iframe Hphys
    ipureintro
    refine ⟨rfl, ⟨[absMsg ty m ents], fun _ Hin => List.mem_singleton.1 Hin, ?_⟩, rfl,
      stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
    rw [toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs
      (by simp [becomeFollower]), toPState_becomeFollower]
    have Hst := Step.higherTerm (cfg := cfg) (id := id) (absMsg ty m ents) (toPState s) Hgt Hto
      (fun h => by simp [absMsg, absMsgFrom, Hfl] at h)
    rw [show (if fromLeader (absMsg ty m ents).ty then (absMsg ty m ents).src else W64 0)
      = W64 0 by simp [absMsg, absMsgFrom, Hfl]] at Hst
    exact Hst

end StepProof

end branches

end EtcdGrove
end Perennial
