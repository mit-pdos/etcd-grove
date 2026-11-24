/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AcksHandler.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `getFastAndSlowAcksHandler(r, desc)` (spec: Proof/swift/AcksSpecs.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewDescDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions]

/-- The handler at the records of one `str` and `delivered` name (round 39, D43 (5)): `deliver`'s
spec is needed only there (an acks handler's record `c'` has `c`'s base, hence its `str`, `γdl`). -/
theorem swift.getFastAndSlowAcksHandler.wp_proofS (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (hRC : ∀ rc bw, Persistent (RC rc bw))
    (str0 : swift.CommandId → GoString) (γdl0 : GName)
    (wp_deliver : swift.Replica.deliver.specE str0 γdl0 MP)
    (c : swift.DC) (hcs : c.str = str0) (hcd : c.γdl = γdl0)
    (hRCe : RC = swift.RCh c.γ c.γc c.γm c.rp) :
    swift.getFastAndSlowAcksHandler.specIc c RC MP := by
  intro γd d x b
  wp_start as #Hctx
  iapply wp_fupd
  wp_auto
  ipersist desc
  ipersist r
  imodintro
  iapply HΦ
  -- round 35 (G-hrec): the spec at every record `c'` of `c`'s base (the code reads only `c.rp`)
  iunfold swift.acksHdOkB
  imodintro
  iintro %c' %hc' #HdR
  have hrp : c.rp = c'.rp := by
    have h := congrArg swift.DC.rp hc'.symm; exact h
  have hctx : c.ctx = c'.ctx := by rw [swift.DC.ctx_base c, ← hc', ← swift.DC.ctx_base c']
  have hs' : c'.str = str0 := by
    rw [← hcs]; exact (show c'.base.str = c.base.str from congrArg swift.DC.str hc')
  have hd' : c'.γdl = γdl0 := by
    rw [← hcd]; exact (show c'.base.γdl = c.base.γdl from congrArg swift.DC.γdl hc')
  have hRCe' : RC = swift.RCh c'.γ c'.γc c'.γm c'.rp := by
    rw [hRCe, ← hrp]
    have h1 : c.γ = c'.γ := (show c.base.γ = c'.base.γ from congrArg swift.DC.γ hc'.symm)
    have h2 : c.γc = c'.γc := (show c.base.γc = c'.base.γc from congrArg swift.DC.γc hc'.symm)
    have h3 : c.γm = c'.γm := (show c.base.γm = c'.base.γm from congrArg swift.DC.γm hc'.symm)
    rw [h1, h2, h3]
  have wp_del : swift.Replica.deliver.specE c'.str c'.γdl MP := by rw [hs', hd']; exact wp_deliver
  clear hs' hd'
  ihave #Hctx' : c'.ctx $$ []
  · rw [← hctx]; iexact Hctx
  iclear Hctx
  irename Hctx' => Hctx
  rw [hrp]
  clear hctx hrp hc' hcs hcd wp_deliver hRCe
  clear c
  revert c'
  intro c hRCe wp_del
  iunfold swift.acksHdOk
  imodintro
  iintro %Rs %ms %q %sz %mem %P %A #Hcap
  unfold replica.mset.handlerOkQ
  iintro %lm %sl %msl
  imodintro
  iintro %Ψ ⟨HR, Hown, Hsl, #Hpre⟩ HΨ
  iunfold replica.mset.handlerPreQ at Hpre
  icases Hpre with ⟨%kms, %Hk, #HL, -⟩
  iunfold replica.mset.leaderOk at HL
  icases HL with (%Hn | #HL)
  · -- no leader message: nothing
    subst Hn
    wp_auto
    iapply HΨ; ileft; iframe HR Hown
  iunfold swift.leadAckP at HL
  icases HL with ⟨%la, %fa, ⟨%Hlm, %Hx, %Hfb, %Hfb0⟩, #Hla, #HlDep, #Hwhy⟩
  subst Hlm
  ihave #Hfa := Hla
  iStructNamed Hfa
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, ⟨#Hra, #HrP⟩, %Hph, #Hpw, #Hdw,
    %Hrp, #HsB, HRs⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -, -, #Hinv, #Hcfg,
    #Hninv, -⟩
  obtain ⟨-, -, hrN, -, -, hk⟩ := Hids
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  -- the commit: the ghost step the first time only (SWB-3); without the row token (G7, round 28)
  -- it is deferred to the proposal (its justification stays in `rowTokO`)
  obtain ⟨r1, r2, r3, r4⟩ := rv
  -- round 54 (D73 (1), the guarded `depWhy`): at a follower with a proposal the descriptor was
  -- accepted before its commit (`leadAckP`'s `accepted` against the row, `rowPhaseOk`)
  ihave Hph2 : iprop(|={⊤}=> swift.epochTok c.γe qe (b, b) ∗ swift.rowTokO c b x dv (r1, r2, r3, r4) ∗
      ⌜c.r ≠ sp.leaderOf c.N b → dv.propose ≠ null → 2 ≤ uint.nat dv.phase⌝) $$ [Het Htok]
  · by_cases hl : c.r = sp.leaderOf c.N b
    · imodintro; iframe Het Htok; ipureintro; intro h; exact absurd hl h
    by_cases hp : dv.propose = null
    · imodintro; iframe Het Htok; ipureintro; intro _ h; exact absurd hp h
    iunfold swift.rowTokO at Htok
    icases Htok with (⟨Htk, Hslt⟩ | ⟨%Hn, Hrest⟩)
    · imod (swift.accepted_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr l qe b (toCmdId x)
        (r1, r2, r3, r4) hrN hk) $$ [Het Htk] with ⟨Het, Htk, %Hra⟩
      · iframe Hinv Hcfg Hninv Het Htk Hwhy
      imodintro; iframe Het
      isplitl [Htk Hslt]
      · iunfold swift.rowTokO; ileft; iframe Htk Hslt
      ipureintro; intro _ hp'
      rcases (Hrp.1.2 hp').2.2.2.2.2 (Or.inl Hra) with h | h
      · exact h
      · exact absurd h.1 hl
    · exact absurd Hn.2 hp
  iapply fupd_wp
  imod Hph2 with ⟨Het, Htok, %Hph2⟩
  imodintro
  -- round B1 (D81): the row facts' proposal clause (`rowAcc`)
  ihave #Hra' := Hra
  iunfold swift.rowAcc at Hra'
  icases Hra' with ⟨-, %Hra2, -⟩
  -- L2 (item 4, D91, D92): with the token (the descriptor has its proposal) the commit happens
  -- at `ghostCommit`'s resolution (a row already committed is committed again,
  -- `recommit_dstep`); without it (no proposal) Go does not resolve (D92's guard) and the commit
  -- is deferred to the proposal (handlePropose's guarded `ghostCommit`)
  ihave Hc : iprop(|={⊤}=> (⌜dv.propose ≠ null⌝ ∗ swift.resolveUpd c.γ c.k (sp.PEv.commit b (toCmdId x))
      iprop(swift.epochTok c.γe qe (b, b) ∗ ∃ r4' : Bool,
      swift.rowTokO c b x { dv with phase := swift.phCOMMIT } (r1, r2, r3, r4') ∗
      (⌜r4' = false⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗ ⌜r4' = true ∨ dv.propose = null⌝ ∗
      (⌜dv.propose = null⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗
      ⌜r4' = true → dv.propose ≠ null⌝)) ∨ (⌜dv.propose = null⌝ ∗ iprop(swift.epochTok c.γe qe (b, b) ∗ ∃ r4' : Bool,
      swift.rowTokO c b x { dv with phase := swift.phCOMMIT } (r1, r2, r3, r4') ∗
      (⌜r4' = false⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗ ⌜r4' = true ∨ dv.propose = null⌝ ∗
      (⌜dv.propose = null⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗
      ⌜r4' = true → dv.propose ≠ null⌝)))
    $$ [Het Htok Hcom]
  · ihave Hsp := swift.rowTokO_commit c b x dv { dv with phase := swift.phCOMMIT } _ rfl
      $$ [Htok]
    · iframe Htok; iright; iexact Hwhy
    icases Hsp with (⟨Htok, Hslt⟩ | ⟨%Hn, Htok⟩)
    · -- round B1 (D81): with the token, the leader entry's acceptance is the row's, so the
      -- descriptor has its proposal (`rowAcc`)
      imod (swift.accepted_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr l qe b (toCmdId x)
        (r1, r2, r3, r4) hrN hk) $$ [Het Htok] with ⟨Het, Htok, %Hr3⟩
      · iframe Hinv Hcfg Hninv Het Htok Hwhy
      have Hpn : dv.propose ≠ null := Hra2 (Or.inr (Or.inr (Or.inl Hr3)))
      imodintro
      ileft
      isplitr
      · ipureintro; exact Hpn
      iunfold swift.resolveUpd
      iintro %W' Hpp
      cases r4
      · imod (swift.commit_dstep' (⊤ \ ↑client.nodeProphN) swift.nodeN_pE swift.spN_pE c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr l qe b
          (toCmdId x) (r1, r2, r3, false) hrN hk rfl W') $$ [Het Htok Hpp]
          with ⟨Het, Htok, Hpost, #Hc⟩
        · iframe Hinv Hcfg Hninv Het Htok Hpp
          iright; ileft; iexact Hwhy
        imodintro; iframe Het Hpost; iexists true
        isplitl [Htok Hslt]
        · iapply swift.rowTokO_of; iframe Htok Hslt
        isplitr; · iright; iexact Hc
        isplitr; · ipureintro; left; rfl
        isplitr; · iright; iexact Hc
        ipureintro; intro _; exact Hpn
      · icases Hcom with (%Hf | #Hc)
        · cases Hf
        imod (swift.recommit_dstep (⊤ \ ↑client.nodeProphN) swift.nodeN_pE swift.spN_pE c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr l qe b
          (toCmdId x) (r1, r2, r3, true) hrN hk rfl W') $$ [Het Htok Hpp]
          with ⟨Het, Htok, Hpost⟩
        · iframe Hinv Hcfg Hninv Het Htok Hpp
        imodintro; iframe Het Hpost; iexists true
        isplitl [Htok Hslt]
        · iapply swift.rowTokO_of; iframe Htok Hslt
        isplitr; · iright; iexact Hc
        isplitr; · ipureintro; left; rfl
        isplitr; · iright; iexact Hc
        ipureintro; intro _; exact Hpn
    · -- no token: no proposal, no step (the commit is deferred to the proposal)
      imodintro
      iright
      isplitr
      · ipureintro; exact Hn.2
      iframe Het; iexists r4; iframe Htok
      have hr4 : r4 = false := by simp [swift.rowEmpty] at Hn; exact Hn.1.2.2.2
      isplitr; · ileft; ipureintro; exact hr4
      isplitr; · ipureintro; right; exact Hn.2
      isplitr; · ileft; ipureintro; exact Hn.2
      ipureintro; intro h; rw [hr4] at h; cases h
  iapply fupd_wp
  imod Hc
  imodintro
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
  wp_auto
  ihave #Hng := swift.DC.ctx_ng c $$ Hctx
  ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
    pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
  · iPkgInit
  try wp_auto
  ipersist leaderFastAck
  wp_join iprop(swift.epochTok c.γe qe (b, b) ∗ ∃ r4' : Bool,
      swift.rowTokO c b x { dv with phase := swift.phCOMMIT } (r1, r2, r3, r4') ∗
      (⌜r4' = false⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗ ⌜r4' = true ∨ dv.propose = null⌝ ∗
      (⌜dv.propose = null⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗
      ⌜r4' = true → dv.propose ≠ null⌝) with [Hc] as ⟨Het, %r4', Htok, #Hcom', %Hph4, #Hcm, %Hpn4⟩
  · icases Hc with (⟨%Hpn, -⟩ | ⟨%Hpn, HQ⟩)
    · exfalso; exact Hpn (show dv.propose = null by first | exact Hif | simpa using Hif)
    try wp_auto
    try wp_join_done
    iexact HQ
  · icases Hc with (⟨%Hpn, Hc⟩ | ⟨%Hpn, -⟩)
    rotate_left
    · exfalso; exact (show dv.propose ≠ null by first | exact Hif | simpa using Hif) Hpn
    try wp_auto
    wp_bind (App (App (Val (@! swift.resolveCommit)) (Val _)) (Val _))
    iapply (swift.wp_resolveCommit c.γ c.k fa.Ballot' fa.CmdId' _) $$ [Hc]
    · iframe #
      isplitr
      · ipureintro; exact Hfb0
      rw [Hfb, Hx]
      iexact Hc
    inext
    iintro HQ
    try wp_auto
    try wp_join_done
    try iexact HQ
  try wp_auto
  ihave %HDlen := ownSlice_len _ _ _ $$ HD
  ihave Hrd : swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp $$ [Hbal HStf Hrcf Het Hxe]
  · iunfold swift.epochRd; iframe; ipureintro; exact Hbw
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  ihave HL : (∃ (i : w64) (dcid : swift.CommandId),
      "i" ∷ i_ptr ↦ i ∗ "dcid" ∷ depCmdId_ptr ↦ dcid ∗
      "Hrd" ∷ swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp ∗
      "HshR" ∷ swift.shOwnR c d b qe ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ dv.D.length⌝ : IProp netDistGF)
    $$ [i depCmdId Hrd HshR]
  · iexists (W64 0), _
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for HL
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z dv.dep.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif) | simpa using Hif
    have hiD : sint.nat i < dv.D.length := by rw [HDlen.1]; word
    obtain ⟨dj, hdj⟩ : ∃ dj, dv.D[sint.nat i]? = some dj :=
      ⟨dv.D[sint.nat i], List.getElem?_eq_getElem hiD⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dv.dep.len := ⟨Hi.1, hlt⟩
    rw [if_pos hb]
    wp_apply wp_load_slice_index (t := swift.CommandId.ty) dv.dep (sint.Z i) dv.D _ dj Hi.1
      $$ [HD] as -
    · iframe HD; ipureintro; exact hdj
    ihave #HdR' := HdR
    iunfold swift.depSpecR at HdR'
    ihave #Hgcd := HdR' $$ %d %qe %b %bw %stp %rcp %dj
    wp_apply Hgcd $$ [Hrd HshR] as %dd ⟨Hrd, HshR, Hdd⟩
    · iframe Hrd Hctx HshR
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; exact ⟨by word, by word⟩
    icases Hdd with (%Hnull | #HdL)
    · exact absurd Hnull Hif
    wp_apply sync.Mutex.wp_Lock $$ [$HdL] as ⟨HdLk, HS⟩
    iunfold swift.succInv at HS
    icases HS with ⟨%ssl, %sl0, Hsucc, Hssl, Hsslcap⟩
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType swift.CommandId.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [fa.CmdId']
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hssl Hsslcap Hlsl] as %nsl ⟨Hssl, Hsslcap, -⟩
    · iframe
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$HdL $HdLk Hsucc Hssl Hsslcap]
    · iunfold swift.succInv; iexists _, _; iframe
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  -- the loop's exit (L2: with the client package imported, `wp_if_destruct` leaves the
  -- condition as a value equality)
  have hnI : ¬ sint.Z i < sint.Z dv.dep.len := by
    first | exact Hif | simpa using Hif | exact fun h => Hif (by simp [h])
  try rw [show decide (sint.Z i < sint.Z dv.dep.len) = false from decide_eq_false hnI]
  try rw [if_pos (decide_eq_true rfl)]
  try wp_auto
  subst Hx
  haveI := hRC rcp bw
  icases HRC with #HRCp
  ihave #HRCh : swift.RCh c.γ c.γc c.γm c.rp rcp bw $$ []
  · rw [← hRCe]; iexact HRCp
  iunfold swift.shOwnR at HshR
  icases HshR with ⟨Hst, HFQ, HrdR, Henv, Hpin⟩
  ihave Hpin : swift.epochPinQ c.γxp qe b $$ [Hpin]
  · iunfold swift.epochPinQ; iexact Hpin
  have hrp' : swift.rowPhaseOk c.N c.r b { dv with phase := swift.phCOMMIT } (r1, r2, r3, r4') :=
    swift.rowPhaseOk_commit c.N c.r b dv _ _ Hrp.1
  iapply fupd_wp
  imod (swift.depWhy_phase c.γ c.γxm c.N c.r b fa.CmdId' dv _ swift.phCOMMIT Hrp.1
    (fun hl hp hle => absurd hle (by have := Hph2 hl hp; omega))) $$ [Hdw] with #Hdw'
  · isplitr
    · iintro - -; imodintro; ipureintro; rfl
    iexact Hdw
  imodintro
  ihave Hslot := swift.slotCapR_slotOkT c MP γd d fa.CmdId' b ms Rs
    (replica.mset.ownD ms q sz mem P A (swift.leadAckP c b fa.CmdId') iprop(True) _)
    { dv with phase := swift.phCOMMIT } (r1, r2, r3, r4') qe Hrp.2
    (swift.msetF_of _ _ _ _ _ _ _ _) $$ Hcap
  ihave #HpwC : swift.phaseWhy c.γ c.N c.r b fa.CmdId' { dv with phase := swift.phCOMMIT } $$ []
  · iapply swift.phaseWhy_ne1; show swift.phCOMMIT ≠ W64 1; unfold swift.phCOMMIT; decide
  ihave #Hrep := swift.repPre_congr c.γ c.N c.r b fa.CmdId' dv { dv with phase := swift.phCOMMIT }
    rfl rfl rfl rfl $$ HrP
  ihave ⟨Htix, Htokw⟩ := swift.rowTokO_tix c b fa.CmdId' { dv with phase := swift.phCOMMIT }
    (r1, r2, r3, r4') $$ Htok
  wp_apply (wp_del c.γ c.γc c.γm c.γl c.γw c.γv c.γe c.γo c.γx c.γxe c.γxm c.γxp c.γxu c.γrp c.γcg c.γout c.γcl c.γdc γd
      c.rp c.rr d c.N c.r c.k qe qe b bw stp rcp { dv with phase := swift.phCOMMIT } fa.CmdId'
      iprop(Rs ∗ replica.mset.ownD ms q sz mem P A (swift.leadAckP c b fa.CmdId') iprop(True) _ ∗
        (swift.tixD c.γxu c.γxm b fa.CmdId' { dv with phase := swift.phCOMMIT } -∗
          swift.rowTokO c b fa.CmdId' { dv with phase := swift.phCOMMIT } (r1, r2, r3, r4')) ∗
        ghostMapElem c.γsh d (DFrac.own (1 : Qp).half) qe ∗ c.env d qe)
      iprop(⌜c.sq = true⌝ ∗ c.ret d fa.CmdId' ∗ c.env d qe))
    $$ [Hrd HrdR Hpin HRs Hown Htokw Htix Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hshe Henv Hslot] as %fin Hfin
  · iframe Hrd HrdR Hpin HRCh HRs Hown Htokw Hshe Henv Hslot HsB Hrep Htix
    isplitr
    · iunfold swift.DC.ctx at Hctx; iexact Hctx
    isplitl [Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs]
    · iunfold swift.descF
      iframe Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL
      isplitl [Hph]
      · iExactEq Hph; rfl
      ipureintro; exact Hop
    isplitr
    · by_cases hpn : dv.propose = null
      · rw [if_neg (by simp [hpn])]; itrivial
      · rw [if_pos (decide_eq_true ⟨rfl, hpn⟩)]
        icases Hcm with (%h | #h)
        · exact absurd h hpn
        · iexact h
    iunfold swift.execWhy
    iframe Hdw'
    ileft; ipureintro; right; right; rfl
  icases Hfin with ⟨Hrd, HrdR, Hpin, Hfin⟩
  iunfold swift.epochPinQ at Hpin
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hfin with ⟨Hd, ⟨HRs, Hown, Htokw, Hshe, Henv⟩, Htix⟩
    ihave Htok := Htokw $$ Htix
    iapply HΨ
    ileft
    iframe Hown
    iunfold swift.descSt
    iexists qe, bw, stp, rcp, { dv with phase := swift.phCOMMIT }, (r1, r2, r3, r4')
    iframe Hrd Hd Htok HRs HRCp Hcom' Hdw' HsB
    isplitl [Hshe Hst HFQ HrdR Henv Hpin]
    · iunfold swift.shOwn; iframe Hshe; iunfold swift.shOwnR; iframe Hst HFQ HrdR Henv Hpin
    isplitr
    · isplitr
      · iunfold swift.rowAcc at Hra; icases Hra with ⟨#Hra1, -, #Hra3⟩
        iunfold swift.rowAcc
        isplitr; · iexact Hra1
        isplitr
        · ipureintro
          rintro (h | h | h | h)
          · exact Hra2 (Or.inl h)
          · exact Hra2 (Or.inr (Or.inl h))
          · exact Hra2 (Or.inr (Or.inr (Or.inl h)))
          · exact Hpn4 h
        iexact Hra3
      iexact Hrep
    isplitr
    · ipureintro; intro _; exact Hph4
    isplitr
    · iapply swift.phaseWhy_ne1; show swift.phCOMMIT ≠ W64 1; unfold swift.phCOMMIT; decide
    ipureintro; exact ⟨hrp', Hrp.2⟩
  · simp only [↓reduceIte]
    icases Hfin with ⟨#Hex, %Hsq, Hret, Henv⟩
    iapply HΨ
    iright
    iunfold swift.descGone
    iframe Hex Hret
    isplitr
    · ipureintro; exact Hsq
    iexists qe, bw, stp, rcp; iframe Hrd
    iunfold swift.shOwnR; iframe Hst HFQ HrdR Henv Hpin


theorem swift.getFastAndSlowAcksHandler.wp_proof (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (hRC : ∀ rc bw, Persistent (RC rc bw))
    (wp_deliver : ∀ c : swift.DC, swift.Replica.deliver.specE c.str c.γdl MP)
    (hRCe : ∀ c : swift.DC, RC = swift.RCh c.γ c.γc c.γm c.rp) :
    swift.getFastAndSlowAcksHandler.specI RC MP := fun c =>
  swift.getFastAndSlowAcksHandler.wp_proofS RC MP hRC c.str c.γdl (wp_deliver c) c rfl rfl (hRCe c)

end proof

end Perennial.github_com.imdea_software.swiftpaxos
