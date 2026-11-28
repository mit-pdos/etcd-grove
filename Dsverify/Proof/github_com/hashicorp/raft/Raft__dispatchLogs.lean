/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__dispatchLogs.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).dispatchLogs` (stage 4: an instance of `leader.dispatch_gen`,
`leader/Dispatch.lean`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Dispatch

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

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.dispatchLogs.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_tryStageCommitIndex : github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec (GF := GF) (hG := hG))
    (wp_match : github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG))
    (wp_setLastLog : github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.dispatchLogs.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s sl dq fs => by
  iintro %Φ ⟨#Hpkg, #Hr, Hm, Hl, Hsl, %Hne, Hfs⟩ HΦ
  ihave ⟨%a, Hsrv, HlastLog, Happ, %Ha, #Hldr, Hrest, Hconf⟩ := mainOwnAt_lopen r γ rc i s $$ Hm
  ihave ⟨%D, %g, Hst, %Hg, Hrest⟩ := mainRest_stV r γ rc i s a $$ Hrest
  ihave Hfs : ([∗list] f ∈ fs, dispOpen γ rc i Kstd f) $$ [Hfs]
  · iapply (BigSepL.bigSepL_mono (fun {k x} _ => dispP_open γ rc i x)) $$ Hfs
  iapply (github_com.hashicorp.raft.leader.dispatch_gen wp_getCurrentTerm wp_getLastIndex
    wp_getCommitIndex wp_tryStageCommitIndex wp_match wp_setLastLog wp_asyncNotifyCh wp_Now
    r γ rc i s sl dq fs a Kstd iprop(True) iprop(True) (replCover γ.srvs i s.log) Hne D g
    (fun es _ hes g' hg' => by
      iintro ⟨#HI, #Hd, Hsrv, Hst, #Hl, Hrc, Htoks, -⟩
      ihave H := storeLogs_app_win γ rc i s es D g' hes hg'
        iprop(srvV rc { s with log := s.log ++ es } ∗ stVS rc D g' ∗
          ([∗list] k ↦ e ∈ es, llogIdx γ s.term (s.log.length + 1 + k) e) ∗ True)
        $$ HI Hd Hsrv Hst [Hrc Htoks]
      · simp only [pendHyps]; iframe; iframe #
      ihave ⟨Hw, Hau⟩ := H $$ []
      · iintro Hs Hst #Hx; imodintro; iframe; iframe #
      iframe))
    $$ [Hsrv Hst HlastLog Happ Hl Hsl Hfs]
  · iframe; iframe #; ipureintro; exact ⟨Hg, Ha.1⟩
  inext
  iintro ⟨%es, %Hes, Hsrv, ⟨%g', Hst, %Hg'⟩, HlastLog, Happ, Hl, Hsl, -, -⟩
  ihave Hrest := Hrest $$ Hst []
  · ipureintro; exact Hg'
  have hnc : ∀ e ∈ es, e.kind ≠ kConfig := by
    intro e he hk
    rcases (Hes.2 e he).2 with h | h | h <;> rw [h] at hk <;> exact absurd hk (by decide)
  have hLT : lastTerm (s.log ++ es) = s.term := by
    have hne' : es ≠ [] := by
      intro h; apply Hne; rw [← List.length_eq_zero_iff, ← Hes.1, h]; rfl
    exact lastTerm_append_ne _ _ _ hne' (fun e he => (Hes.2 e he).1)
  ihave Hconf := confOwn_append_noCfg r γ i s a es hnc $$ Hconf
  ihave Hl := leaderOwnM_mono r γ rc i s.term _ (replCover γ.srvs i (s.log ++ es)) _
    (replCover_append_noCfg γ.srvs i s.log es hnc) $$ Hl
  iapply HΦ
  iexists { s with log := s.log ++ es }
  isplitl [Hsrv HlastLog Happ Hrest Hconf]
  · ihave Hrest := (mainRest_log r γ rc i s a (s.log ++ es)).2 $$ Hrest
    iapply mainOwnAt_lclose r γ rc i { s with log := s.log ++ es } a
    simp only [hLT]
    iframe; iframe #
    ipureintro; exact Ha
  have hgrow : s.log.length < (s.log ++ es).length := by
    have : es.length ≠ 0 := by
      intro h; apply Hne; rw [← List.length_eq_zero_iff, ← Hes.1, h]
    simp only [List.length_append]; omega
  isplitr; · ipureintro; exact ⟨rfl, hgrow⟩
  iframe

end proof

end Perennial
