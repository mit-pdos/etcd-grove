/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgApp_gt.v.

One term case of `Step`'s `MsgApp` branch (the incoming term is higher:
`becomeFollower(m.Term, m.From)`, then `stepFollower`), in its own file so that it
checks in parallel with the others; `proof_raft__Step_MsgApp.v` combines them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may `Require` it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem` (closing `∀ m' ∈ recv, m' = …` goals: `elem_of_app`,
  `list_elem_of_singleton`, `elem_of_nil`, `naive_solver`) and `wp_load_step` (the load
  of `r.step` in `r.step(r, m)`, bound by hand with `raft.wp_load_step`, as `wp_apply`
  does not find a load in function position) are not ported.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.repl_lemmas

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

theorem wp_Step_MsgApp_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgApp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    -- protocol facts the dispatch derives from the ghost state (`app_recv_wf`,
    -- `app_no_conflict_below_commit`)
    PlogWf (entryID.mk m.LogTerm' m.Index') ents →
    uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
    (∀ e ∈ ents, e.Type' = EntryNormal) →
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
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents ∗
        "Hcap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .app m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hconf Hgt
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hgt]
  wp_auto
  repeat (rw [Hty]; wp_auto)
  -- "received a message with higher term"
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_raft_log
  repeat (rw [Hty]; wp_auto)
  -- `becomeFollower(m.Term, m.From)`: a leader's message
  wp_apply _P.becomeFollower _ _ _ _ _ _ (by exact Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
  repeat (rw [Hty]; wp_auto)
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  have Hsf : ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).stepfn =
      functions stepFollower [] := rfl
  rw [Hsf]
  wp_apply _P.stepFollower cfg r id { becomeFollower s m.Term' m.From' with prvals := pvs } m
      ents (zero_val _) [] (.inr (.inr (.inl Hty)))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun _ => ⟨Hpwf, Hnw, Hnorm, Hconf, Hfid⟩)
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
    $$ [$Hphys Hcap] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · isplitl []
    · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    · iintro %_; iframe Hents Hcap
  obtain ⟨rfl, Happ⟩ := followerStepResult_app _ _ _ _ _ _ _ Hty Hres
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
    app_frame Hty Happ (NetFrame.refl _) (Int.le_of_lt Hgt) (Int.le_max_right _ _)⟩
  refine ⟨[absMsg .app m ents] ++ [absMsg .app m ents], ?_, ?_⟩
  · intro m' Hm'; simpa using Hm'
  · refine Step.trans _ _ _ _ _
      (step_higher_term_leader cfg id (toPState s) .app m ents rfl Hgt Hto Hfid) ?_
    exact step_handle_app cfg id _ _ m ents s1
      (adopt_after_stepdown s m.Term' m.From' pvs) Hto rfl (by simp [pbecomeFollower])
      Hconf Happ Hfid

end StepProof

end branches

end EtcdGrove
end Perennial
