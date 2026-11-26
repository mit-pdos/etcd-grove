/-
#33 S4 (P-raft-4), `notes/antithesis-rawnode-design.md` §2.1, §2.6. **The `RawNode` API's laws,
proved** (`RawNodeApi.lean`'s `.law` statements), and its specs from the strengthened ones:
- the laws read out of `rawNode` (`ownRawNodeAt … true`): each persistent fact is one of
  `ownRaftGhost`'s at the node's protocol reading (`rawNode_ghost`), the log's boundary `base0`
  from the scope (`RnScopeBasic`), so the full log before the boundary is empty; the term ceiling raised
  (`ownRawNodeAt_raise_tc`, `ownRawNode_raise_tc`'s proof at the protocol state);
- the term budget's laws over the sealed names (`InvNodeChan.lean`'s; `termLB_rb`'s proof restated,
  `TracedNodeRun.lean`'s, to keep the traced cone out of this module's imports);
- each `RawNode.<F>.apiSpec` from its `absSpec` at the scope flag `true` (`apiSpec_of_abs`), and
  `NewRawNode.emptyStartApiSpec` from `NewRawNode.spec` (`RawNodeStart.lean`'s
  `wp_proofEmptyStartAbs`); `Ready`'s and `HasReady`'s over their proofs
  (`RawNode.<F>.wp_apiProof`, with those proofs' callee specs as hypotheses).

`rawNode_vote.law` is of the client's durable state (`ownDurGhost`), not of `rawNode`: a vote a
`Step` grants has no `isVote` until a `Ready`'s *enter* persists it; it is read through the slot
invariant (`rawNode_vote`).
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeApi
import all Proof.go_etcd_io.raft.v3.RawNodeApi
public import Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import Proof.go_etcd_io.raft.v3.RawNodeStart
public import Proof.go_etcd_io.raft.v3.RawNodeStartApi
public import Proof.go_etcd_io.raft.v3.RawNode__ReadyAbs
public import Proof.go_etcd_io.raft.v3.RawNode__HasReadyAbs
public import Proof.go_etcd_io.raft.v3.RawNode__StepAbs
public import Proof.go_etcd_io.raft.v3.RawNode__TickAbs
public import Proof.go_etcd_io.raft.v3.RawNode__CampaignAbs
public import Proof.go_etcd_io.raft.v3.RawNode__ProposeAbs
public import Proof.go_etcd_io.raft.v3.RawNode__AdvanceAbs
public import Proof.go_etcd_io.raft.v3.RawNode__ReportUnreachableAbs
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
theorem rawNode_ghost (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState)
    (qs : List Msg) (ip : Nat) (Q : IProp GF) [Persistent Q]
    (HQ : ∀ (s : NState) (md : Bool), toPState s = r.p → RnScopeBasic rs s → rs.term = s.term →
      uint.Z rs.term ≤ uint.Z rs.tc → ownRaftGhost γ id r.p md ⊢ Q) :
    rawNode γ {} rn id rs r qs ip ⊢ Q ∗ rawNode γ {} rn id rs r qs ip := by
  refine persistent_entails_right ?_
  unfold rawNode ownRawNodeAt
  iintro H
  iNamed H
  icases rnScopeAt_scope true rs s $$ Hsc with ⟨%Hscope, -⟩
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hg, -⟩
  have Hp : toPState s = r.p := by rw [← Hps]; rfl
  rw [← Hp] at HQ
  iapply HQ s _ rfl (Hscope rfl) Htrm (by rw [Htrm, Hpvoff.2.1]; exact Hpvoff.2.2.1) $$ Hg

/-- The scope's log boundary, at the protocol reading. -/
theorem rnScope_base {rs : RNState} {s : NState} {r : RState} (Hps : toPState s = r.p)
    (H : RnScopeBasic rs s) : r.p.base = base0 := by
  rw [← Hps]; exact H.2.2.2.2.2.1

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
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc Htrm _ => ?_)
  have Hb := rnScope_base Hps Hsc
  iintro Hg
  icases (entails_wand (persistent_entails_left (ownRaftGhost_logOk γ id r.p))) $$ Hg
    with ⟨Hg, %Hlo⟩
  icases ownRaftGhost_logRecs γ id r.p md $$ Hg with ⟨%Hw, -⟩
  ipureintro
  have h2 := Hlo.2.2
  rw [Hb] at Hw h2
  refine ⟨Hw, h2, ?_⟩
  rw [Htrm, ← Hps]; rfl

theorem rawNode_noSnap : rawNode_noSnap.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro -
  ipureintro
  obtain ⟨-, -, -, -, Hsl, Hprev, -, Hout, -⟩ := Hsc
  rw [← Hps]
  exact ⟨Hprev, Hsl, Hout⟩

theorem rawNode_logTerms : rawNode_logTerms.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro Hg
  icases ownRaftGhost_terms_le γ id r.p $$ Hg with ⟨%Ht, Hg⟩
  icases ownRaftGhost_logRecs γ id r.p md $$ Hg with ⟨%Hw, -⟩
  ipureintro
  intro e he
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
  have hk' : r.p.log[k]? = some e := by rw [List.getElem?_eq_getElem hk, hke]
  exact Ht e.Index' e.Term' (plogTermAt_lookup r.p.base r.p.log e.Index' k e hk' (Hw k e hk'))

theorem rawNode_scope : rawNode_scope.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (persistent_entails_right ?_)
  unfold rawNode ownRawNodeAt
  iintro H
  iNamed H
  icases rnScopeAt_scope true rs s $$ Hsc with ⟨%Hscope, Hsc⟩
  icases rnScopeAt_cfgIn true rs s $$ Hsc with ⟨%Hcin, -⟩
  ipureintro
  obtain ⟨H1, H2, H3, -⟩ := Hcin rfl
  exact ⟨H1, H3, fun h => ⟨H2 h, (Hscope rfl).1 h⟩⟩

theorem rawNode_phsTerm : rawNode_phsTerm.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (persistent_entails_right ?_)
  unfold rawNode ownRawNodeAt
  iintro H
  iNamed H
  ipureintro
  subst Hps
  exact Hphs.1.1

theorem rawNode_logRecs : rawNode_logRecs.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  have Hb := rnScope_base Hps Hsc
  rw [← Hb]
  iintro Hg
  icases ownRaftGhost_logRecs γ id r.p md $$ Hg with ⟨-, #Hr⟩
  iexact Hr

theorem rawNode_leader : rawNode_leader.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  have Hb := rnScope_base Hps Hsc
  by_cases hr : r.p.role = .leader
  · iintro Hg
    icases (entails_wand (persistent_entails_left (wand_entails
      (ownRaftGhost_isLeader (md := md) γ id r.p hr)))) $$ Hg with ⟨Hg, #Hl⟩
    iunfold ownRaftGhost at Hg
    icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
    iNamed H
    icases ownLogGhost_lead_full γ id r.p kl (virt V πc) hr $$ Hl Hlg with ⟨⟨%fp, #Hp, #Hpf, -⟩, -⟩
    icases lpfull_fp γ id r.p.term r.p.base r.p.log fp $$ Hpf with ⟨-, %Hfp⟩
    have hfp : fp = [] := by rw [Hb] at Hfp; exact fullOk_base0 Hfp.1
    subst hfp
    ihave #Hf := leadFull_intro γ id r.p.term r.p.base r.p.log [] $$ Hp Hpf
    icases leadFull_camp γ r.p.term ([] ++ r.p.log) $$ Hf with ⟨%ldr, %F0, #Hl2, #Hc, %Hpre⟩
    icases isLeader_unique γ id ldr r.p.term $$ Hl Hl2 with %Heq
    subst Heq
    iintro !> -
    iframe Hl
    iexists F0
    iframe Hc
    ipureintro; simpa using Hpre
  · iintro -
    iintro !> %h
    exact absurd h hr

/-- The durable state's vote: the slot invariant's entered fragments (`durFrags`), its maps the
durable half's (`durShares_agree`), which hold the vote at the term (`VoteHistOkD`). -/
theorem rawNode_vote : rawNode_vote.law (GF := GF) := by
  intro γ id S
  iintro H
  iunfold ownDurGhost at H
  icases H with ⟨%E, Hsh, #Hp, #Hslot, #HI1⟩
  ihave %Hvh : ⌜VoteHistOkD E.voted S⌝ $$ []
  · iunfold durPers at Hp
    icases Hp with ⟨%kd, %fp, %Hpure, -⟩
    ipureintro; exact Hpure.1
  by_cases hv : S.vote = W64 0
  · imodintro
    isplitr
    · iintro !> %h; exact absurd hv h
    iunfold ownDurGhost
    iexists E
    iframe Hsh Hp Hslot HI1
  have Hlk : E.voted !! S.term = some S.vote := by rw [Hvh.2, if_neg hv]
  have HE : (↑(slotN γ id) : CoPset) ⊆ ↑(raftN γ) := slotN_raftN γ id
  unfold slotInv
  iinv Hslot with Hb Hclose
  unfold slotBody
  icases Hb with ⟨%γs', %E', %g, %Mq, >%Hγs', >Hsh', >#Hfr, Hai, >Hv', >Hg, >Hq, >%Hdom, >%Hcur,
    >%Hb⟩
  icases durShares_agree γ id _ _ E E' $$ Hsh Hsh' with ⟨Hsh, Hsh', %HEE⟩
  subst HEE
  ihave #Hvt : isVote (GF := GF) γ id S.term S.vote $$ []
  · iunfold durFrags at Hfr
    icases Hfr with ⟨#Hvs, -⟩
    iapply BigSepM.bigSepM_lookup (Φ := fun t c => isVote (GF := GF) γ id t c) Hlk $$ Hvs
  imod Hclose $$ [Hsh' Hai Hv' Hg Hq] with -
  · inext
    iexists γs', E, g, Mq
    isplitr; · ipureintro; exact Hγs'
    iframe Hsh' Hfr Hai Hv' Hg Hq
    ipureintro; exact ⟨Hdom, Hcur, Hb⟩
  imodintro
  isplitr
  · iintro !> -; iexact Hvt
  iunfold ownDurGhost
  iexists E
  unfold slotInv slotBody
  iframe Hsh Hp Hslot HI1

theorem rawNode_tally : rawNode_tally.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  iexact Htally

theorem rawNode_commit : rawNode_commit.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  have Hb := rnScope_base Hps Hsc
  iintro Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases ownLogGhost_commitIn γ id r.p kl (virt V πc) $$ Hlg with ⟨%fp, %Hfp, -, -, #Hc⟩
  have hfp : fp = [] := by rw [Hb] at Hfp; exact fullOk_base0 Hfp.1
  subst hfp
  iExactEq Hc
  rw [List.nil_append]

theorem rawNode_committed : rawNode_committed.law (GF := GF) := by
  intro γ rn id rs r qs ip
  iintro H
  icases rawNode_ghost γ rn id rs r qs ip (isCommitted γ (r.p.log.take (uint.nat r.p.commit)))
    (fun s md Hps Hsc _ _ => by
      have Hb := rnScope_base Hps Hsc
      iintro Hg
      icases ownRaftGhost_cmt γ id r.p $$ Hg with ⟨%fp, %Hfp, -, #Hc⟩
      have hfp : fp = [] := by rw [Hb] at Hfp; exact fullOk_base0 Hfp
      subst hfp
      iExactEq Hc
      unfold cprefix; rw [List.nil_append, toNat_uZ]) $$ H with ⟨#Hc, H⟩
  imodintro
  iframe Hc H

theorem rawNode_commitInv : rawNode_commitInv.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  exact wand_entails (ownRaftGhost_inv_md (md := md) γ id r.p)

theorem rawNode_entries : rawNode_entries.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc _ _ => ?_)
  iintro Hg
  icases ownRaftGhost_logRecs γ id r.p md $$ Hg with ⟨%Hw, #Hr⟩
  iapply logRecs_entData γ r.p.base r.p.log Hw $$ Hr

theorem rawNode_term_tc : rawNode_term_tc.law (GF := GF) := by
  intro γ rn id rs r qs ip
  refine entails_wand (rawNode_ghost γ rn id rs r qs ip _ fun s md Hps Hsc Htrm Htc => ?_)
  iintro -
  ipureintro
  rw [← Hps]; show uint.Z s.term ≤ _; rw [← Htrm]; exact Htc

/-- **The term ceiling raised, at the protocol state** (`ownRawNode_raise_tc`'s proof, through
`ownRawNodeAt_intro`): only the ghost ceiling moves, so the protocol reading, the queue, the
in-progress boundary and the scope are the same. -/
theorem ownRawNodeAt_raise_tc (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState)
    (qs : List Msg) (ip : Nat) (sc : Option RnMode) (tc : w64) (Hle : uint.Z rs.tc ≤ uint.Z tc) :
    ⊢ ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc -∗
      ownRawNodeAt γ rn id { rs with tc := tc } r qs ip sc := by
  iintro H
  iNamed H
  have Hle' : uint.Z s.gh.tc ≤ uint.Z tc := by rw [← Hpvoff.2.1]; exact Hle
  ihave Hphys := ownRaftPhysC_raise_tc cf _ id s tc Hle' $$ Hphys
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with gh := { s.gh with tc := tc } }) rfl rfl rfl rfl $$ Hghost
  ihave Hsc := rnScopeAt_keepAll sc rs { rs with tc := tc } s { s with gh := { s.gh with tc := tc } }
    (fun _ h => h) rfl $$ Hsc
  obtain ⟨H1, -, H3, H4, H5⟩ := Hpvoff
  iapply ownRawNodeAt_intro γ rn id { rs with tc := tc } r qs ip sc
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
  intro γ rn id rs r qs ip tc Hle
  unfold rawNode
  exact ownRawNodeAt_raise_tc γ rn id rs r qs ip (some {}) tc Hle

/-- **The storage handshake, at the protocol state** (`ownRawNode_appended`'s proof, through
`ownRawNodeAt_intro`): only the log's unpersisted entries move, which neither the protocol reading,
the in-progress boundary nor the scope reads. -/
theorem ownRawNodeAt_appended (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState)
    (qs : List Msg) (ip : Nat) (sc : Option RnMode) (Hsl : rs.slent = none) (a : List EntryM)
    (Ha : a ≠ [] → ∀ e0, rs.unpersisted.head? = some e0 →
      uint.nat e0.Index' - 1 + a.length ≤ rs.delivered.length) :
    ⊢ ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc -∗ appendReceipt rs.storage rs.unpersisted a ==∗
      ownRawNodeAt γ rn id { rs with unpersisted := [] } r qs ip sc := by
  iintro H Htok
  iNamed H
  ihave Htok : appendReceipt s.logst.storage s.logst.unpersisted a $$ [Htok]
  · rw [← Hstor.1, ← Hunp]; iexact Htok
  icases ownRaftPhysC_log_at cf rnv.raft' id s $$ Hphys with ⟨Hlog, %Hgh0, Hlback⟩
  imod ownRaftLog_absorb s.log s.logst a (fun hne e0 he => by
      have := Ha hne e0 (by rw [Hunp]; exact he); rw [Hdlen] at this
      have := uint_Z_nonneg s.logst.applying
      have : uint.nat s.logst.applying = (uint.Z s.logst.applying).toNat := rfl
      omega) $$ Hlog Htok with Hlog
  ihave Hphys := Hlback $$ %_ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
    %(fun _ => logLast_le_of_fields rfl rfl rfl)
  ihave Hghost := ownStepGhost_congr γ _ cf id (s := s)
    (s' := { s with logst := { s.logst with unpersisted := [] } }) rfl rfl rfl rfl $$ Hghost
  ihave Hsc := rnScopeAt_keepAll sc rs { rs with unpersisted := [] } s
    { s with logst := { s.logst with unpersisted := [] } } (fun _ h => h) rfl $$ Hsc
  imodintro
  iapply ownRawNodeAt_intro γ rn id { rs with unpersisted := [] } r qs ip sc
    { s with logst := { s.logst with unpersisted := [] } } cf fp rnv sv hprev steps Hwf Hin Hasync
    Hdlen rfl Hsnap
    (stepsOk_mono s _ rs.steps rfl ⟨rfl, rfl⟩ (Int.le_refl _) rfl (Int.le_refl _) Hstok)
    Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
    ⟨Hloan.1, Hloan.2.1, (fun l (h : rs.slent = some l) => by rw [Hsl] at h; cases h),
        Hloan.2.2.2⟩
    Hsdt Hrole Hphs Hps Hip $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv
      Hstrecs Hloanc Hsloc Hhist [Hledger] [Hdur] [Hrntr] Hsc
  · unfold restoreLedger restoreClock queuedRestoreTerms localInstallations; iexact Hledger
  · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) $$ Hdur
  · iapply rnTrace_congr γ _ id cf (s := s)
      (s' := { s with logst := { s.logst with unpersisted := [] } }) rfl rfl rfl rfl rfl $$ Hrntr

theorem rawNode_appended : rawNode_appended.law (GF := GF) := by
  intro γ rn id rs r qs ip a Hsl Ha
  unfold rawNode
  exact ownRawNodeAt_appended γ rn id rs r qs ip (some {}) Hsl a Ha

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

/-- The scope's guard at `sc = true`: the mode `{}`. -/
private theorem true_eq_true_eq : (fun md : RnMode => basicScope true = some md) = (fun md => md = {}) := by
  funext md; apply propext; simp only [basicScope, Option.some.injEq]; exact eq_comm

theorem RawNode.Step.apiSpec_of_abs (H : RawNode.Step.absSpec (GF := GF) (hG := hG)) :
    RawNode.Step.apiSpec (GF := GF) (hG := hG) := by
  have h := H true; rw [true_eq_true_eq] at h; exact h

theorem RawNode.Tick.apiSpec_of_abs (H : RawNode.Tick.absSpec (GF := GF) (hG := hG)) :
    RawNode.Tick.apiSpec (GF := GF) (hG := hG) := by
  have h := H true; rw [true_eq_true_eq] at h; exact h

theorem RawNode.Campaign.apiSpec_of_abs (H : RawNode.Campaign.absSpec (GF := GF) (hG := hG)) :
    RawNode.Campaign.apiSpec (GF := GF) (hG := hG) := by
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

theorem RawNode.ReportUnreachable.apiSpec_of_abs
    (H : RawNode.ReportUnreachable.absSpec (GF := GF) (hG := hG)) :
    RawNode.ReportUnreachable.apiSpec (GF := GF) (hG := hG) := by
  have h := H {} rfl rfl; exact h

theorem RawNode.HasReady.apiSpec_of_abs (H : RawNode.HasReady.absSpec (GF := GF) (hG := hG)) :
    RawNode.HasReady.apiSpec (GF := GF) (hG := hG) := by
  intro γ rn id rs r qs ip
  wp_start_folded as H'
  iNamed H'
  iunfold rawNode at Hrn
  wp_apply H true γ rn id rs r qs ip $$ [$Hrn] as %b Hb
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

/-- **`RawNode.Step`, over `rawNode`** (`RawNode.Step.wp_absProof`'s hypotheses). -/
theorem RawNode.Step.wp_apiProof
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    RawNode.Step.apiSpec (GF := GF) (hG := hG) :=
  RawNode.Step.apiSpec_of_abs
    (RawNode.Step.wp_absProof wp_IsResponseMsg wp_IsLocalMsg wp_IsLocalMsgTarget wp_raft_Step
      wp_GetType wp_GetFrom)

/-- **`RawNode.Tick`, over `rawNode`** (`RawNode.Tick.wp_absProof`'s hypotheses). -/
theorem RawNode.Tick.wp_apiProof
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    RawNode.Tick.apiSpec (GF := GF) (hG := hG) :=
  RawNode.Tick.apiSpec_of_abs (RawNode.Tick.wp_absProof wp_tickElection wp_tickHeartbeat)

/-- **`RawNode.Campaign`, over `rawNode`** (`RawNode.Campaign.wp_absProof`'s hypotheses). -/
theorem RawNode.Campaign.wp_apiProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.Campaign.apiSpec (GF := GF) (hG := hG) :=
  RawNode.Campaign.apiSpec_of_abs (RawNode.Campaign.wp_absProof wp_raft_Step wp_MessageType_Enum)

/-- **`RawNode.Propose`, over `rawNode`** (`RawNode.Propose.wp_absProof`'s hypotheses). -/
theorem RawNode.Propose.wp_apiProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.Propose.apiSpec (GF := GF) (hG := hG) :=
  RawNode.Propose.apiSpec_of_abs (RawNode.Propose.wp_absProof wp_raft_Step wp_MessageType_Enum)

/-- **`RawNode.Advance`, over `rawNode`** (`RawNode.Advance.wp_absProof`'s hypothesis). -/
theorem RawNode.Advance.wp_apiProof (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Advance.apiSpec (GF := GF) (hG := hG) :=
  RawNode.Advance.apiSpec_of_abs (RawNode.Advance.wp_absProof wp_raft_Step)

/-- **`RawNode.ReportUnreachable`, over `rawNode`** (`RawNode.ReportUnreachable.wp_absProof`'s hypotheses). -/
theorem RawNode.ReportUnreachable.wp_apiProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.ReportUnreachable.apiSpec (GF := GF) (hG := hG) :=
  RawNode.ReportUnreachable.apiSpec_of_abs
    (RawNode.ReportUnreachable.wp_absProof wp_raft_Step wp_MessageType_Enum)

/-- **`NewRawNode` restarting into `rawNode` at a mode without snapshots or configuration
changes**: `NewRawNode.restartAtSpec (some md)` (`NewRawNode_restartAt_impl`), the ghost prefix
empty at the boundary `base0` (`RestartScopeOk`'s snapshots conjunct). -/
theorem NewRawNode.wp_proofRestartAtApi
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG)) :
    NewRawNode.restartAtApiSpec (GF := GF) (hG := hG) := by
  unfold NewRawNode.restartAtApiSpec
  intro md Hsn _Hcc γ N c cv lok si σ csm a m S F SV hpSV hSV H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx Happ
    Ha1 Ha2 Hboot Hcs Hnsm Htlk HtrC HSh Hsc x
  wp_start_folded as ⟨Hc, Hlg, Hcl, Hvac, Hfits, HrS, Hconf, Hrs, #Hcap⟩
  wp_apply (ApiImpl.RawNodeStart.NewRawNode_restartAt_impl (some md) wp_NewRawNode γ N c cv lok si
      σ csm a m S F SV hSV H1 H2 H3 H4 H5 H6 H7 H8 H9 Hmx Happ Ha1 Ha2 Hboot Hcs Hnsm Htlk HtrC HSh
      (fun md' h => by cases h; exact Hsc) x)
    $$ [Hc Hlg Hcl Hvac Hfits HrS Hconf Hrs]
    as %rn %err ⟨%Herr, %l, %sn, %g, %K, %fp, Hrn, %Hfp, #Hcm, %Hl, Hgen, Hfree, HrS, HF⟩
  · iframe Hc Hlg Hcl Hvac Hfits HrS Hconf Hrs
    iintro !> %md' %h %hs; iexact Hcap
  obtain rfl : fp = [] := Hfp (Hsc.2.2.2.2 Hsn)
  iapply HΦ
  isplitr; · ipureintro; exact Herr
  iexists l, sn, g, K
  unfold rawNode
  iframe Hrn Hcm Hgen Hfree HrS HF
  ipureintro; exact Hl

end specs

end EtcdGrove
end Perennial
