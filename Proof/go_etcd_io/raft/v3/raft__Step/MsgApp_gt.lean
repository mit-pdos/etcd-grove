/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgApp_gt.v.

One term case of `Step`'s `MsgApp` branch (the incoming term is higher:
`becomeFollower(m.Term, m.From)`, then `stepFollower`), in its own file so that it
checks in parallel with the others; `proof_raft__Step_MsgApp.v` combines them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may `Require` it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac`s `recv_elem` (closing `∀ m' ∈ recv, m' = …` goals: `elem_of_app`,
  `list_elem_of_singleton`, `elem_of_nil`, `naive_solver`) and `wp_load_step` (the load
  of `r.step` in `r.step(r, m)`, bound by hand with `raft.wp_load_stepC`, as `wp_apply`
  does not find a load in function position) are not ported.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.repl_lemmas
public import Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

set_option maxHeartbeats 1000000 in
theorem wp_Step_MsgApp_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) :
    m.Type' = MsgApp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    NStateWf s →
    -- protocol facts the dispatch derives from the ghost state (`app_recv_wf`,
    -- `app_no_conflict_below_commit`)
    PlogWf (entryID.mk m.LogTerm' m.Index') ents →
    uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
    (uint.Z s.logst.committed ≤ uint.Z m.Index' →
     PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents)
       (entryID.mk m.LogTerm' m.Index') →
     plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents = W64 0 ∨
     uint.Z s.logst.committed <
       uint.Z (plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents)) →
    -- this file: the incoming term is higher: `becomeFollower(m.Term, m.From)`, then
    -- `stepFollower`
    uint.Z s.term < uint.Z m.Term' →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .app m ents) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ ∗
        -- (D22 S-d3b) a truncation's mark (`AppTrunc`)
        "%Htrunc" ∷ ⌜AppTrunc m ents s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw Hconf Hgt
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
  rw [decide_eq_true Hgt]
  wp_auto
  wp_drive _Q
  -- "received a message with higher term"
  wp_drive _Q
  wp_raft_logC
  wp_drive _Q
  -- `becomeFollower(m.Term, m.From)`: a leader's message
  wp_apply _P.becomeFollower _ _ _ _ _ _ (by exact Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
  wp_drive _Q
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  have Hsf : ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).stepfn =
      functions stepFollower [] := rfl
  rw [Hsf]
  ihave #Hsrc0 : tsSrc (GF := GF) ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).logst.storage m.Type' sn $$ []
  · iapply tsSrc_ne; notsnap_tac
  wp_apply _P.stepFollower c ∅ r id { becomeFollower s m.Term' m.From' with prvals := pvs } ml m ents sn rs (zero_val _) ctx (.inr (.inr (.inl Hty)))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne)) (by intro _; simp only [becomeFollower, resetTo, resetTo0]; exact Hterm)
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun _ => ⟨Hpwf, Hnw, Hconf, Hfid, fun h => by simp [becomeFollower] at h⟩)
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
    (by notfwd_tac) $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
  · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
  obtain ⟨rfl, rfl, Happ⟩ := followerStepResult_app _ _ _ _ _ _ _ _ Hty Hres
  have Hwf1 : NStateWf
      { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
          lead := m.From' } := ⟨rfl, rfl⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  iapply HΦ $$ %interface.nil %s1
  iframe Hphys
  ipureintro
  refine ⟨nstateWf_handle_app _ _ _ _ _ Hwf1 Happ, ?_, rfl,
    and_assoc.mp ⟨app_frame Hty Happ (NetFrame.refl _) (Int.le_of_lt Hgt) (Int.le_max_right _ _),
    trunc_handle_app Happ rfl rfl⟩⟩
  refine ⟨[absMsg .app m ents] ++ [absMsg .app m ents], ?_, ?_⟩
  · intro m' Hm'; simpa using Hm'
  · refine StepCD.frame ?_ (RFrame.trans (by rframe) (rframe_handle_app _ _ _ _ _ Happ))
    refine StepCF.trans _ _ _ _ _
      (step_higher_term_leader c id (toPState s) .app m ents [] rfl Hgt Hto Hfid) ?_
    exact step_handle_app c id _ _ m ents s1
      (adopt_after_stepdown s m.Term' m.From' pvs) Hto rfl (by simp [pbecomeFollower])
      Hconf Happ Hfid

end StepProof

end branches

end EtcdGrove
end Perennial
