/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap_lt.v.

One term case of `Step`'s `MsgSnap` branch (the incoming term is stale: logged and
dropped), in its own file so that it checks in parallel with the others; `MsgSnap.lean`
combines them. Proof structure, not specification: no `Module Type`, no `Parameter`;
only files in this directory may import it.

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as their second.
* Rocq's `Local Ltac recv_elem` (closes `∀ m' ∈ recv, m' = a` for `recv` built from
  `[]` and `[a]`) is not ported.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.repl_lemmas
public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

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

set_option maxHeartbeats 1000000 in
theorem wp_Step_MsgSnap_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (sv : SnapshotM) (scfg : CSLists) :
    m.Type' = MsgSnap →
    m.To' = id →
    m.Term' ≠ W64 0 →
    NStateWf s →
    -- this file: the incoming term is stale: logged and dropped
    uint.Z m.Term' < uint.Z s.term →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absSnap m sv scfg) ∧
            StepCDS c c (snapCfg sv scfg) id B (snapId sv) s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        -- (2026-10-19, D21 M3) the no-snapshot mode kept
        "%Hng" ∷ ⌜s'.gh = s.gh⌝ }} := by
  intro Hty Hto Hterm Hwf Hlt
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  rw [decide_eq_false Hterm]
  wp_auto
  wp_drive _Q
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  wp_auto
  wp_drive _Q
  rw [decide_eq_true Hlt]
  wp_auto
  -- (checkQuorum || preVote) && (MsgHeartbeat || MsgApp): with either on, the type test is
  -- false
  -- (2026-10-20) joined at `false` (`wp_join`): the rest of the arm is verified once, not
  -- once per flag case
  wp_join (v := #false) at (If (If _ (Val #true) _) _ (Val #false)) with [Hphys r m Hm]
  · wp_drive _Q
    cq_split _Q
    -- where the type test ran, its last disjunct (`MsgApp`) is the value left
    all_goals first
      | wp_join_done
      | (isplitr
         · ipureintro; rw [decide_eq_false (by w32_ne)]
         iframe)
  -- not MsgPreVote, not MsgStorageAppendResp: only the log line
  try wp_auto
  wp_drive _Q
  wp_raft_logC
  iapply HΦ $$ %interface.nil %s
  iframe Hphys
  ipureintro
  exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil,
    StepCDS.frame (.refl _) (RFrame.refl _)⟩, rfl, rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
