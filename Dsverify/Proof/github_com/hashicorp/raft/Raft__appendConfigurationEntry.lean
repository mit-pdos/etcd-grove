/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__appendConfigurationEntry.lean (241f27e).
-/
/-
The proof of `raft.Raft.appendConfigurationEntry` (stage 4).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__appendConfigurationEntry
public import Dsverify.Spec.github_com.hashicorp.raft.nextConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.EncodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__setConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__startStopReplication
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Dispatch
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Ccf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

theorem github_com.hashicorp.raft.Raft.appendConfigurationEntry.wp_proof
    (wp_nextConfiguration : github_com.hashicorp.raft.nextConfiguration.spec (GF := GF) (hG := hG))
    (wp_EncodeConfiguration : github_com.hashicorp.raft.EncodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_tryStageCommitIndex : github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec (GF := GF) (hG := hG))
    (wp_match : github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG))
    (wp_setLastLog : github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration : github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG))
    (wp_setConfiguration : github_com.hashicorp.raft.commitment.setConfiguration.spec (GF := GF) (hG := hG))
    (wp_startStopReplication : github_com.hashicorp.raft.Raft.startStopReplication.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.appendConfigurationEntry.spec (GF := GF) (hG := hG) := by
  intro r γ rc i s f tid
  wp_start as ⟨#Hr, Hm, Hl, Hf, ⟨%k, %p, #Hcm, %Hk⟩, Htid⟩
  ihave ⟨#HInv, #Hsrvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave %Hcv := isRaft_cv r γ rc i $$ Hr
  ihave #HdurI := isRaft_durInv r γ rc i $$ Hr
  ihave ⟨%a, Hsrv, Hpw, HlastLog, Happ, %Ha, #Hldr, Hrest, Hconf⟩ := mainOwnAtSt_open r γ rc i s $$ Hm
  ihave ⟨%D, %g, Hst, %Hg, Hrest⟩ := mainRest_stV r γ rc i s a $$ Hrest
  iunfold confOwnSt at Hconf
  icases Hconf with ⟨%cfg, %ccfg, %cidx, Hconfs, #Hcfg, #Hccfg, %Hli1, #Hcmt, Hcc, %n0, #Hn0, Hcix, #Hcl0⟩
  have Hli : uint.nat cidx = lastCfgIdx s.log ∧ (cidx = cidx ∨
      (uint.nat cidx = lastCfgIdx (s.log.take (uint.nat cidx - 1)) ∧ a < uint.nat cidx)) :=
    ⟨Hli1, Or.inl rfl⟩
  ihave #Hcl : (⌜cidx ≠ cidx ∨ uint.nat cidx ≤ n0⌝ ∨
      ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat cidx ≤ k⌝ : IProp GF) $$ []
  · icases Hcl0 with (%h | Hk)
    · ileft; ipureintro; right; exact h
    · iright; iexact Hk
  unfold ccfP
  icases Hf with ⟨%rq, %lv, %t, %v, Hreq, %Hrq, Hlog, Hresp, Hdisp, Hde⟩
  imod ccfgOwn_entry γ ⊤ (by solve_ndisj) i s.term (lastCfgIdx s.log) $$ [Hcc] with ⟨Hcc, %e0, #He0, %He0k⟩
  · iframe; iframe #
  iapply wp_ncmod _ _ rfl (srvV_llogIdx_leader γ rc i s (lastCfgIdx s.log) e0)
  isplitl [Hsrv]; · iframe; iframe #
  iintro ⟨Hsrv, %Hent0⟩
  iapply wp_ncmod _ _ rfl (srvV_facts γ rc i s)
  isplitl [Hsrv]; · iframe; iframe #
  iintro ⟨Hsrv, -, %Hfacts⟩
  have hli1 : 1 ≤ uint.nat cidx := by rw [Hli.1]; exact (proto.ent_le_length Hent0).1
  ihave Hcfg' := Hcfg
  iunfold cfgAtIs at Hcfg'
  icases Hcfg' with (⟨%h0, -⟩ | ⟨%ss, %ec, Hcv0, %Hec⟩)
  · exfalso; omega
  iunfold cfgVal at Hcv0
  icases Hcv0 with ⟨#Hss, %Hssok⟩
  wp_auto
  wp_apply (wp_nextConfiguration γ cfg ss DFrac.discard cidx rq) $$ [$Hss] as %c' %err ⟨-, Hres⟩
  · ipureintro; exact ⟨Hssok, Hrq⟩
  icases Hres with (⟨%Herr, %ss', Hss', %Hss'⟩ | ⟨#HerrOk, %Hleaf⟩)
  rotate_left
  · ihave #HerrOk' := HerrOk
    iunfold errOk at HerrOk'
    icases HerrOk' with ⟨%x, %Hx, -⟩
    subst Hx
    wp_auto
    wp_apply (deferError.respond_ccf wp_respond f cfgChangeQ (GoInterface.ok x)) $$ [Hde] as -
    · ileft; iframe; unfold cfgChangeQ; iright; iright; iframe #; ipureintro; exact Hleaf
    iapply HΦ
    iexists s
    iframe Hl Htid
    isplitl
    rotate_left
    · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
    ihave Hrest := Hrest $$ Hst []
    · ipureintro; exact Hg
    iapply mainOwnAt_lclose r γ rc i s a
    iframe Hsrv Hpw HlastLog Happ Hrest
    iframe #
    isplitr; · ipureintro; exact Ha
    iapply confOwn_intro r γ i s a cfg ccfg cidx cidx n0 Hli
    iframe; iframe #
  subst Herr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  iunfold raftImm at Himm
  icases Himm with ⟨#Hpv, -⟩
  wp_auto
  wp_apply (wp_EncodeConfiguration c' ss' (DFrac.own 1)) $$ [$Hss'] as %b ⟨Hss', Hb⟩
  imod ownSlice_persist $$ Hb with #Hb
  imod ownSlice_persist $$ Hss' with #Hss'
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType (go.GoType.PointerType logFuture.ty))))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType logFuture.ty)
    [f.[configurationChangeFuture, go!"logFuture"]]
  wp_auto
  isplitl []; · ipureintro; rfl
  iintro %nsl ⟨Hnsl, -⟩
  wp_auto
  ihave Hdo : ([∗list] q ∈ [f.[configurationChangeFuture, go!"logFuture"]],
      dispOpen γ rc i (fun k d => k = kConfig ∧ d = encodeServers ss') q) $$ [Hlog Hresp Hdisp Hde]
  · iapply BigSepL.bigSepL_singleton.2
    unfold dispOpen
    iexists _, t, v, encodeServers ss', []
    iframe Hlog Hresp Hdisp
    iframe #
    isplitr; · iapply ownSlice_nil
    isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    iright; iright; iright; iframe; ipureintro; rfl
  have hcur : cfgOfC γ.cv s.log = srvVoters ss := by
    unfold cfgOfC cfgAtC
    rw [← Hli.1, Hec.2.1]
    show γ.cv ec.data = _
    rw [Hec.2.2.2, Hcv]
    exact cfgDec_encode _ _ Hssok
  have hwin : ∀ es : RLog, es.length = [f.[configurationChangeFuture, go!"logFuture"]].length →
      (∀ e ∈ es, e.term = s.term ∧ (fun k d => k = kConfig ∧ d = encodeServers ss') e.kind e.data) →
      ∀ g' : w64, uint.nat g' ≤ s.dur.1 →
      (gprot.Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗ stVS rc D g' ∗ leaderIs γ s.term i ∗
        receipt es.length ∗
        ([∗list] e ∈ es.filter (fun e => decide (e.kind = kCommand)), ∃ n, opTok γ e.data n) ∗
        (ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ commitIs γ s.term k p) ⊢
        |==> (logWin γ rc i (.store (s.log.length + 1) es) ∗
        (logWin γ rc i (.store (s.log.length + 1) es) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
          rc.ownL A ∗ (rc.ownL (A.store (s.log.length + 1) es) ={∅, ⊤ \ ↑storeN}=∗
            srvV rc { s with log := s.log ++ es } ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗ stVS rc D g' ∗
            ([∗list] j ↦ e ∈ es, llogIdx γ s.term (s.log.length + 1 + j) e) ∗
            ccfgOwn γ i s.term (lastCfgIdx s.log))))) := by
    intro es hlen hes g' hg'
    obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp hlen
    have he := hes e (List.mem_singleton.2 rfl)
    have hcv' : cfgValid γ.srvs (γ.cv e.data) := by
      rw [Hcv, he.2.2, cfgDec_encode _ _ Hss'.1]; exact srvsOk_cfgValid _ _ Hss'.1
    have hadj : adjV (cfgOfC γ.cv s.log) (γ.cv e.data) := by
      rw [hcur, he.2.2, Hcv, cfgDec_encode _ _ Hss'.1]; exact Hss'.2
    iintro ⟨#HI, #Hd, Hsrv, Hpw, Hst, #Hl, Hrc, -, Hcc, #Hcm⟩
    ihave H := storeLogs_cfg_win γ rc i s e k p D g' ⟨he.1, he.2.1, hcv', hadj, Hk⟩ hg'
      iprop(srvV rc { s with log := s.log ++ [e] } ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗ stVS rc D g' ∗
        ([∗list] j ↦ e' ∈ [e], llogIdx γ s.term (s.log.length + 1 + j) e') ∗
        ccfgOwn γ i s.term (lastCfgIdx s.log))
      $$ HI Hd Hpw Hsrv Hst [Hrc Hcc]
    · simp only [pendHyps]; iframe; iframe #
    iapply H
    iintro Hpw Hs Hst Hcc #Hx; imodintro; iframe
    iapply BigSepL.bigSepL_singleton.2
    rw [Nat.add_zero]; iexact Hx
  wp_apply (leader.dispatch_gen wp_getCurrentTerm wp_getLastIndex wp_getCommitIndex
    wp_tryStageCommitIndex wp_match wp_setLastLog wp_asyncNotifyCh wp_Now r γ rc i s _ (DFrac.own 1)
    [f.[configurationChangeFuture, go!"logFuture"]] a _
    iprop(ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ commitIs γ s.term k p)
    (ccfgOwn γ i s.term (lastCfgIdx s.log)) (replCover γ.srvs i s.log) (by simp) D g hwin)
    $$ [$Hr $Hsrv $Hpw $Hst $HlastLog $Happ $Hldr $Hl $Hnsl $Hdo $Hcc $Hcm]
    as ⟨%es, %Hes, Hsrv, Hpw, ⟨%g', Hst, %Hg'⟩, HlastLog, Happ, Hl, Hnsl, Hcc, #Hptrs⟩
  · ipureintro; exact ⟨Hg, Ha.1⟩
  obtain ⟨hlen, hes⟩ := Hes
  obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨heT, heK, heD⟩ := hes e (List.mem_singleton.2 rfl)
  simp only [List.map_cons, List.map_nil] at *
  ihave Hp := BigSepL.bigSepL_singleton.1 $$ Hptrs
  icases Hp with ⟨%e', %He', Hp⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at He'
  subst He'
  iunfold logPtr at Hp
  icases Hp with ⟨%lv', #Hlp, Hlis⟩
  iunfold logIs at Hlis
  icases Hlis with ⟨%Hlv', -, -⟩
  iStructNamed Hlp
  wp_method_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave #Hrconf := isRaft_conf r γ rc i $$ Hr
  iunfold raftConf at Hrconf
  icases Hrconf with ⟨%cc0, -, -, #HlatInv⟩
  wp_apply (wp_setLatestConfiguration false r γ ccfg cfg cidx cidx c' lv'.Index' ss' DFrac.discard null)
    $$ [$Hconfs $Hss'] as ⟨Hconfs, -, -⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iframe #; ipureintro; exact Or.inr Hss'.1
  have hdl : s.dur.1 ≤ s.log.length := Hfacts.2.1
  have hidx : uint.nat lv'.Index' = s.log.length + 1 := Hlv'.1
  have hlast : lastCfgIdx (s.log ++ [e]) = s.log.length + 1 := lastCfgIdx_append_cfg s.log e heK
  have hent : ent (s.log ++ [e]) (s.log.length + 1) = some e := by
    rw [proto.ent_append_right _ _ _ (by omega)]; simp [ent]
  have hLT : lastTerm (s.log ++ [e]) = s.term :=
    lastTerm_append_ne s.log [e] s.term (by simp) (by simp [heT])
  ihave #Hcfg2 : cfgAtIs γ (s.log ++ [e]) (s.log.length + 1) c' $$ []
  · iunfold cfgAtIs; iright; iexists ss', e
    iunfold cfgVal
    iframe #
    ipureintro; exact ⟨Hss'.1, by omega, hent, heK, heD⟩
  ihave ⟨%cc, %sd, %cm, Hccf, #Hccn, Hsdf, #Hsdn, Hcmf, #Hcmi, Hback⟩ := leaderOwnM_fields $$ Hl
  wp_auto
  wp_apply (wp_setConfiguration γ rc i { s with log := s.log ++ [e] } cm c' (lastCfgIdx s.log))
    $$ [$Hcmi $HInv $HdurI $Hsrv $Hldr $Hcc] as ⟨Hsrv, Hcc⟩
  · simp only
    rw [hlast]
    iframe #
    ipureintro; exact ⟨by omega, Hcv⟩
  ihave Hl := Hback $$ Hccf Hsdf Hcmf
  ihave Hl := leaderOwnM_mono r γ rc i s.term _ (fun _ => True) _ (fun _ _ => trivial) $$ Hl
  ihave Hrest := Hrest $$ Hst []
  · ipureintro; exact Hg'
  ihave Hrest := (mainRest_log r γ rc i s a (s.log ++ [e])).2 $$ Hrest
  ihave #Hccfg2 := cfgAtIs_append γ s.log [e] _ ccfg $$ Hccfg
  ihave %Hcle := cfgAtIs_le γ s.log _ ccfg $$ Hccfg
  ihave #Hcmt2 := (cmtIdx_mono γ s.term s.term s.log (s.log ++ [e]) (uint.nat cidx) (Nat.le_refl _)
    (proto.ent_append_left _ _ _ Hcle)) $$ Hcmt
  ihave #Hcl2 : (⌜cidx ≠ lv'.Index' ∨ uint.nat lv'.Index' ≤ n0⌝ ∨
      ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat lv'.Index' ≤ k⌝ : IProp GF) $$ []
  · ileft; ipureintro; left; intro h
    have := (lastCfgIdx_spec s.log).1
    rw [h, hidx] at Hli1; omega
  ihave Hconf := confOwn_intro r γ i { s with log := s.log ++ [e] } a c' ccfg cidx lv'.Index' n0
    ⟨by simp only; rw [hidx, hlast], Or.inr ⟨by simp only; rw [hidx, Nat.add_sub_cancel,
      take_append_le' _ _ _ (Nat.le_refl _), List.take_length]; exact Hli.1, by omega⟩⟩ $$ [Hconfs Hcc Hcix]
  · simp only
    rw [hidx, hlast]
    iframe; iframe #
  ihave Hm := mainOwnAt_lclose r γ rc i { s with log := s.log ++ [e] } a $$ [Hsrv Hpw HlastLog Happ Hrest Hconf]
  · simp only
    rw [hLT]
    iframe; iframe #
    ipureintro; exact Ha
  wp_apply (wp_startStopReplication r γ rc i { s with log := s.log ++ [e] } tid) $$ [$Hr $Hm $Hl $Htid]
    as ⟨Hm, Hl, Htid⟩
  iapply HΦ
  iexists { s with log := s.log ++ [e] }
  iframe
  ipureintro; exact ⟨rfl, by simp⟩

end proof

end Perennial
