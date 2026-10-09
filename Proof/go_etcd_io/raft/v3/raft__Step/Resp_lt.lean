/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_Resp_lt.v.

The lower-term case of `Step`'s `MsgAppResp` and `MsgHeartbeatResp` branches, for both
types at once, in its own file so that it checks in parallel with the other term cases
-- see `MsgAppResp.lean` and `MsgHeartbeatResp.lean`, which combine them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac` `ne_ty` is not ported
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

/-- `m.Term < r.Term` for a `MsgAppResp` or `MsgHeartbeatResp`: with `checkQuorum` and
`preVote` both off, and the type neither `MsgPreVote` nor `MsgStorageAppendResp`, the
stale message is only logged, then `return nil`. `Step.refl`, nothing received. -/
theorem wp_Step_Resp_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ty : MsgType) :
    m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp →
    m.Term' ≠ W64 0 →
    uint.Z m.Term' < uint.Z s.term →
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
  intro Hty Hterm Hlt Hwf
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ (uint.Z s.term < uint.Z m.Term') by omega)]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hlt]
  wp_auto
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  wp_apply raft.wp_load_preVote $$ Hphys as Hphys
  rcases Hty with Hty | Hty <;> cases s.prevote <;> wp_auto
  all_goals iterate 6 (try (rw [Hty]; wp_auto))
  all_goals
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
