/-
#33 S4 (P-raft-4), `notes/antithesis-rawnode-design.md` §2.1, §2.6. **The `RawNode` API's laws,
proved** (`RawNodeApi.lean`'s `.law` statements), and its specs from the strengthened ones:
- the laws read out of `rawNode` (`ownRawNodeAt … true`): each persistent fact is one of
  `ownRaftGhost`'s at the node's protocol reading (`rawNode_ghost`), the log's boundary `base0`
  from the scope (`RnScope`), so the full log before the boundary is empty; the term ceiling raised
  (`ownRawNodeAt_raise_tc`, `ownRawNode_raise_tc`'s proof at the protocol state);
- the term budget's laws over the sealed names (`InvNodeChan.lean`'s; `termLB_rb`'s proof restated,
  `TracedNodeRun.lean`'s, to keep the traced cone out of this module's imports);
- each `RawNode.<F>.apiSpec` from its `absSpec` at the scope flag `true` (`apiSpec_of_abs`), and
  `NewRawNode.emptyStartApiSpec` from `NewRawNode.spec` (`RawNodeStart.lean`'s
  `wp_proofEmptyStartAbs`); `Ready`'s and `HasReady`'s over their proofs
  (`RawNode.<F>.wp_apiProof`, with those proofs' callee specs as hypotheses).

Not proved: `rawNode_vote.law` (false as stated: a vote granted by a `Step` is a promise in the
virtual maps until the next `Ready`'s *enter* mints its `isVote`, `Protocol/Enter.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeApi
import all Proof.go_etcd_io.raft.v3.RawNodeApi
public import Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import Proof.go_etcd_io.raft.v3.RawNodeStart
public import Proof.go_etcd_io.raft.v3.RawNode__ReadyAbs
public import Proof.go_etcd_io.raft.v3.RawNode__HasReadyAbs
import all Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A persistent fact of `rawNode`'s ghost state**: any `Q` that `ownRaftGhost` at the protocol
reading gives, with the scope's facts, the term and its ceiling. -/
theorem rawNode_ghost (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState)
    (qs : List Msg) (ip : Nat) (Q : IProp GF) [Persistent Q]
    (HQ : ∀ (s : NState) (md : Bool), toPState s = ps → RnScope rs s → rs.term = s.term →
      uint.Z rs.term ≤ uint.Z rs.tc → ownRaftGhost γ id ps md ⊢ Q) :
    rawNode γ rn id rs ps qs ip ⊢ Q ∗ rawNode γ rn id rs ps qs ip := by
  refine persistent_entails_right ?_
  unfold rawNode ownRawNodeAt
  iintro H
  iNamed H
  icases rnScopeAt_scope true rs s $$ Hsc with ⟨%Hscope, -⟩
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hg, -⟩
  subst Hps
  iapply HQ s _ rfl (Hscope rfl) Htrm (by rw [Htrm, Hpvoff.2.1]; exact Hpvoff.2.2.1) $$ Hg

/-- The scope's log boundary, at the protocol reading. -/
theorem rnScope_base {rs : RNState} {s : NState} {ps : PState} (Hps : toPState s = ps)
    (H : RnScope rs s) : ps.base = base0 := by
  subst Hps; exact H.2.2.2.2.2.1

/-- The full log before the boundary `base0` is empty. -/
theorem fullOk_base0 {fp : List EntryM} (H : FullOk base0 fp) : fp = [] := by
  have h := H.1; rw [base0_index] at h; exact List.eq_nil_of_length_eq_zero (by omega)

/-- A well-formed log's records give each entry's data. -/
theorem logRecs_entData (γ : RaftNames) (b : entryID) (es : List EntryM) (Hwf : PlogWf b es) :
    logRecs (GF := GF) γ b es ⊢ [∗list] e ∈ es, entData γ e := by
  have Hr := PlogWf_range b es Hwf
  unfold logRecs
  refine BigSepL.bigSepL_mono fun {k e} hk => ?_
  have hlt := (List.getElem?_eq_some_iff.1 hk).1
  have : uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 := by unfold plogLastIndexZ at Hr; omega
  rw [if_pos this]
  iintro ⟨%pt, -, #He⟩
  iapply isEntryR_data γ e pt $$ He

theorem rawNode_wf : rawNode_wf.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc Htrm _ => ?_)
  have Hb := rnScope_base Hps Hsc
  iintro Hg
  icases (entails_wand (persistent_entails_left (ownRaftGhost_logOk γ id ps))) $$ Hg
    with ⟨Hg, %Hlo⟩
  icases ownRaftGhost_logRecs γ id ps md $$ Hg with ⟨%Hw, -⟩
  ipureintro
  have h2 := Hlo.2.2
  rw [Hb] at Hw h2
  refine ⟨Hw, h2, ?_⟩
  rw [Htrm, ← Hps]; rfl

theorem rawNode_noSnap : rawNode_noSnap.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro -
  ipureintro
  obtain ⟨-, -, -, -, Hsl, Hprev, -, Hout⟩ := Hsc
  subst Hps
  exact ⟨Hprev, Hsl, Hout⟩

theorem rawNode_scope : rawNode_scope.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro -
  ipureintro; exact Hsc.1

theorem rawNode_logRecs : rawNode_logRecs.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  have Hb := rnScope_base Hps Hsc
  rw [← Hb]
  iintro Hg
  icases ownRaftGhost_logRecs γ id ps md $$ Hg with ⟨-, #Hr⟩
  iexact Hr

theorem rawNode_leader : rawNode_leader.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  have Hb := rnScope_base Hps Hsc
  by_cases hr : ps.role = .leader
  · iintro Hg
    icases (entails_wand (persistent_entails_left (wand_entails
      (ownRaftGhost_isLeader (md := md) γ id ps hr)))) $$ Hg with ⟨Hg, #Hl⟩
    iunfold ownRaftGhost at Hg
    icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
    iNamed H
    icases ownLogGhost_lead_full γ id ps kl (virt V πc) hr $$ Hl Hlg with ⟨⟨%fp, #Hp, #Hpf, -⟩, -⟩
    icases lpfull_fp γ id ps.term ps.base ps.log fp $$ Hpf with ⟨-, %Hfp⟩
    have hfp : fp = [] := by rw [Hb] at Hfp; exact fullOk_base0 Hfp.1
    subst hfp
    ihave #Hf := leadFull_intro γ id ps.term ps.base ps.log [] $$ Hp Hpf
    icases leadFull_camp γ ps.term ([] ++ ps.log) $$ Hf with ⟨%ldr, %F0, #Hl2, #Hc, %Hpre⟩
    icases isLeader_unique γ id ldr ps.term $$ Hl Hl2 with %Heq
    subst Heq
    iintro !> -
    iframe Hl
    iexists F0
    iframe Hc
    ipureintro; simpa using Hpre
  · iintro -
    iintro !> %h
    exact absurd h hr

theorem rawNode_tally : rawNode_tally.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  iexact Htally

theorem rawNode_commit : rawNode_commit.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  have Hb := rnScope_base Hps Hsc
  iintro Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases ownLogGhost_commitIn γ id ps kl (virt V πc) $$ Hlg with ⟨%fp, %Hfp, -, -, #Hc⟩
  have hfp : fp = [] := by rw [Hb] at Hfp; exact fullOk_base0 Hfp.1
  subst hfp
  iExactEq Hc
  rw [List.nil_append]

theorem rawNode_committed : rawNode_committed.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  iintro H
  icases rawNode_ghost γ rn id rs ps qs ip (isCommitted γ (ps.log.take (uint.nat ps.commit)))
    (fun s md Hps Hsc _ _ => by
      have Hb := rnScope_base Hps Hsc
      iintro Hg
      icases ownRaftGhost_cmt γ id ps $$ Hg with ⟨%fp, %Hfp, -, #Hc⟩
      have hfp : fp = [] := by rw [Hb] at Hfp; exact fullOk_base0 Hfp
      subst hfp
      iExactEq Hc
      unfold cprefix; rw [List.nil_append, toNat_uZ]) $$ H with ⟨#Hc, H⟩
  imodintro
  iframe Hc H

theorem rawNode_commitInv : rawNode_commitInv.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  exact wand_entails (ownRaftGhost_inv_md (md := md) γ id ps)

theorem rawNode_entries : rawNode_entries.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro Hg
  icases ownRaftGhost_logRecs γ id ps md $$ Hg with ⟨%Hw, #Hr⟩
  iapply logRecs_entData γ ps.base ps.log Hw $$ Hr

theorem rawNode_term_tc : rawNode_term_tc.law (GF := GF) := by
  intro γ rn id rs ps qs ip
  refine entails_wand (rawNode_ghost γ rn id rs ps qs ip _ fun s md Hps Hsc Htrm Htc => ?_)
  iintro -
  ipureintro
  rw [← Hps]; show uint.Z s.term ≤ _; rw [← Htrm]; exact Htc

/-- **The term ceiling raised, at the protocol state** (`ownRawNode_raise_tc`'s proof, through
`ownRawNodeAt_intro`): only the ghost ceiling moves, so the protocol reading, the queue, the
in-progress boundary and the scope are the same. -/
theorem ownRawNodeAt_raise_tc (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ps : PState)
    (qs : List Msg) (ip : Nat) (sc : Bool) (tc : w64) (Hle : uint.Z rs.tc ≤ uint.Z tc) :
    ⊢ ownRawNodeAt (GF := GF) γ rn id rs ps qs ip sc -∗
      ownRawNodeAt γ rn id { rs with tc := tc } ps qs ip sc := by
  iintro H
  iNamed H
  have Hle' : uint.Z s.gh.tc ≤ uint.Z tc := by rw [← Hpvoff.2.1]; exact Hle
  ihave Hphys := ownRaftPhysC_raise_tc cf _ id s tc Hle' $$ Hphys
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with gh := { s.gh with tc := tc } }) rfl rfl rfl rfl $$ Hghost
  ihave Hsc := rnScopeAt_keep sc rs { rs with tc := tc } s { s with gh := { s.gh with tc := tc } }
    (fun h => h) rfl $$ Hsc
  obtain ⟨H1, -, H3, H4, H5⟩ := Hpvoff
  iapply ownRawNodeAt_intro γ rn id { rs with tc := tc } ps qs ip sc
    { s with gh := { s.gh with tc := tc } } cf fp
    rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp Hsnap
    (stepsOk_mono s _ _ rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl Hle' Hstok) Htrm Hstor
    ⟨H1, rfl, Int.le_trans H3 Hle', fun h => Int.le_trans (H4 h) Hle', H5⟩ Hrs_out Hrs_unst Hrs_clb Hrnfl
    ⟨Hloan.1, Hloan.2.1, Hloan.2.2.1, Hloan.2.2.2⟩
    Hsdt Hrole Hphs Hps Hip $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs
      Hloanc Hsloc Hhist [Hledger] [Hdur] [Hrntr] Hsc
  · unfold restoreLedger restoreClock queuedRestoreTerms localInstallations; iexact Hledger
  · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) $$ Hdur
  · iapply rnTrace_congr γ _ id cf (s := s) (s' := { s with gh := { s.gh with tc := tc } }) rfl rfl rfl
      rfl rfl $$ Hrntr

theorem rawNode_raise_tc : rawNode_raise_tc.law (GF := GF) := by
  intro γ rn id rs ps qs ip tc Hle
  unfold rawNode
  exact ownRawNodeAt_raise_tc γ rn id rs ps qs ip true tc Hle

/-! ### The term budget -/

theorem rnBudget_persistent : rnBudget_persistent.law (GF := GF) := by
  intro γ; unfold rnBudget; infer_instance

theorem rnTermLB_persistent : rnTermLB_persistent.law (GF := GF) := by
  intro γ t; unfold rnTermLB; infer_instance

theorem raftState_open_rn : raftState_open_rn.law (GF := GF) := by
  intro γ id S
  unfold rnTermLB rnBudget
  exact raftState_open γ id S

theorem rnBudget_spend : rnBudget_spend.law (GF := GF) := by
  intro γ t E HE
  unfold rnBudget rnTermLB
  exact budget_spend γ.budget t E HE

theorem rnBudget_step : rnBudget_step.law (GF := GF) := by
  intro γ t1 t2 P _ E HE
  unfold rnBudget rnTermLB
  exact budget_step γ.budget t1 t2 P E HE

theorem rnTermLB_le : rnTermLB_le.law (GF := GF) := by
  intro γ t t' h
  unfold rnTermLB
  exact termLB_le γ.budget t t' h

theorem rnTermLB_bound : rnTermLB_bound.law (GF := GF) := by
  intro γ t E HE
  unfold rnBudget rnTermLB
  exact termLB_bound γ.budget t E HE

/-- `TracedNodeRun.lean`'s `termLB_rb`, restated over the sealed names. -/
theorem rnTermLB_rb : rnTermLB_rb.law (GF := GF) := by
  intro γ t E HE
  unfold rnBudget rnTermLB
  iintro #Hinv #Hlb
  iinv Hinv with >Hi Hclose
  unfold budgetInv
  icases Hi with ⟨%M, %k, HM, Hk, %Hb⟩
  unfold termLB
  ihave %Hle := monoNatLbOwn_valid γ.budget.bound 1 M (uint.nat t) $$ HM Hlb
  imod receipt_snapshot k $$ Hk with ⟨Hk, #Hp⟩
  ihave %Hkl := preceipt_lt k $$ Hp
  imod Hclose $$ [HM Hk] with -
  · inext; iexists M, k; iframe HM Hk; ipureintro; exact Hb
  imodintro
  ipureintro
  have h3 : k < receiptBound GF := Hkl
  omega

end laws

/-! ### The API specs, from the strengthened ones -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The scope's guard at `sc = true`. -/
private theorem true_eq_true_eq : (true = true) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩

theorem RawNode.Step.apiSpec_of_abs (H : RawNode.Step.absSpec (GF := GF) (hG := hG)) :
    RawNode.Step.apiSpec (GF := GF) (hG := hG) := by
  have h := H true; rw [true_eq_true_eq] at h; exact h

theorem RawNode.Tick.apiSpec_of_abs (H : RawNode.Tick.absSpec (GF := GF) (hG := hG)) :
    RawNode.Tick.apiSpec (GF := GF) (hG := hG) := by
  have h := H true; rw [true_eq_true_eq] at h; exact h

theorem RawNode.Propose.apiSpec_of_abs (H : RawNode.Propose.absSpec (GF := GF) (hG := hG)) :
    RawNode.Propose.apiSpec (GF := GF) (hG := hG) := by
  have h := H true; rw [true_eq_true_eq] at h; exact h

theorem RawNode.Ready.apiSpec_of_abs (H : RawNode.Ready.absSpec (GF := GF) (hG := hG)) :
    RawNode.Ready.apiSpec (GF := GF) (hG := hG) := by
  have h := H true; rw [true_eq_true_eq] at h; exact h

theorem RawNode.Advance.apiSpec_of_abs (H : RawNode.Advance.absSpec (GF := GF) (hG := hG)) :
    RawNode.Advance.apiSpec (GF := GF) (hG := hG) := by
  have h := H true; rw [true_eq_true_eq] at h; exact h

theorem RawNode.HasReady.apiSpec_of_abs (H : RawNode.HasReady.absSpec (GF := GF) (hG := hG)) :
    RawNode.HasReady.apiSpec (GF := GF) (hG := hG) := by
  intro γ rn id rs ps qs ip
  wp_start_folded as H'
  iNamed H'
  iunfold rawNode at Hrn
  wp_apply H true γ rn id rs ps qs ip $$ [$Hrn] as %b Hb
  iapply HΦ
  icases Hb with (⟨%Hb, Hrn⟩ | ⟨%Hb, %Hid, ⟨-, Hrn⟩⟩)
  · unfold rawNode; iframe Hrn; ipureintro; intro h; rw [Hb] at h; cases h
  · unfold rawNode; iframe Hrn; ipureintro; intro _; exact Hid trivial

theorem NewRawNode.emptyStartApiSpec_of_abs
    (H : NewRawNode.emptyStartAbsSpec (GF := GF) (hG := hG)) :
    NewRawNode.emptyStartApiSpec (GF := GF) (hG := hG) := H

/-- **`NewRawNode` at an empty storage, over `rawNode`**. -/
theorem NewRawNode.wp_proofEmptyStartApi
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG)) :
    NewRawNode.emptyStartApiSpec (GF := GF) (hG := hG) :=
  NewRawNode.emptyStartApiSpec_of_abs (NewRawNode.wp_proofEmptyStartAbs wp_NewRawNode)

/-- **`RawNode.Ready`, over `rawNode`** (`RawNode.Ready.wp_absProof`'s hypotheses). -/
theorem RawNode.Ready.wp_apiProof
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG)) :
    RawNode.Ready.apiSpec (GF := GF) (hG := hG) :=
  RawNode.Ready.apiSpec_of_abs
    (RawNode.Ready.wp_absProof wp_RawNode_readyWithoutAccept wp_RawNode_acceptReady)

/-- **`RawNode.HasReady`, over `rawNode`** (`RawNode.HasReady.wp_absProof`'s hypotheses). -/
theorem RawNode.HasReady.wp_apiProof
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableEnts : raftLog.hasNextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextCommittedEnts :
      raftLog.hasNextCommittedEnts.spec (GF := GF) (hG := hG))
    (wp_raft_softState : raft.softState.spec (GF := GF) (hG := hG))
    (wp_raft_hardState : raft.hardState.spec (GF := GF) (hG := hG)) :
    RawNode.HasReady.apiSpec (GF := GF) (hG := hG) :=
  RawNode.HasReady.apiSpec_of_abs
    (RawNode.HasReady.wp_absProof wp_SoftState_equal wp_IsEmptyHardState wp_isHardStateEqual
      wp_raftLog_hasNextUnstableSnapshot wp_raftLog_hasNextUnstableEnts
      wp_raftLog_hasNextCommittedEnts wp_raft_softState wp_raft_hardState)

end specs

end EtcdGrove
end Perennial
