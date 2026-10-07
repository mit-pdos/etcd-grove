/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap_lt.v.

One term case of `Step`'s `MsgSnap` branch (the incoming term is stale: logged and
dropped), in its own file so that it checks in parallel with the others; `MsgSnap.lean`
combines them. Proof structure, not specification: no `Module Type`, no `Parameter`;
only files in this directory may import it.

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as their second.
* Rocq's `Local Ltac recv_elem` (closes `∀ m' ∈ recv, m' = a` for `recv` built from
  `[]` and `[a]`) is not ported.
-/
import EtcdGrove.Raft.Proof.raft__Step.repl_lemmas

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

theorem wp_Step_MsgSnap_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (sv : raftpb.Snapshot) (voters : List w64) :
    m.Type' = MsgSnap →
    m.To' = id →
    m.Term' ≠ W64 0 →
    NStateWf s →
    -- this file: the incoming term is stale: logged and dropped
    uint.Z m.Term' < uint.Z s.term →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absSnap m sv voters) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hwf Hlt
  wp_start as Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hlt]
  wp_auto
  -- (checkQuorum || preVote) && (MsgHeartbeat || MsgApp): `checkQuorum` is off; with
  -- pre-vote on, the type test is false
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  wp_apply raft.wp_load_preVote $$ Hphys as Hphys
  -- not MsgPreVote, not MsgStorageAppendResp: only the log line
  cases s.prevote
  all_goals
    wp_auto
    repeat (rw [Hty]; wp_auto)
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
