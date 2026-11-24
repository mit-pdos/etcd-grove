/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleProposeProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.handlePropose(pm, desc, cmdId)` (swift.go:495; P4) against `swift.Replica.handlePropose.specI`
(HandlePropose.lean), round 14 (notes/prove-swift.md §20).

* `swift.pt_halves`: two halves of a typed points-to are the whole.
* Round 47 (46-2, D61 (2)): `swift.claim_rowTok_false` (a claim's token is in the store, so a held
  token of the same key refutes it: a set proposal at `handlePropose` is impossible),
  `swift.locLb_cmd_agree`, `swift.repPre_prop` (the proposal's reply facts, `descSt`'s `repPre`).
  (`descOwn_rest` and `descOwn_check`, unused, are gone: they changed `hs` freely.)
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ProposePure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PoolFnsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BatcherFastDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.IdBound
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Store
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeProofDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [sp.GobFmt]
variable [swift.Assumptions]

end lemmas

section ctx
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

end ctx

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions] [replica.Assumptions] [sync.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

set_option maxHeartbeats 2000000 in
/-- **`handlePropose`** (see the file header; open steps marked). -/
theorem swift.Replica.handlePropose.wp_proof (RC : Loc → w32 → IProp netDistGF)
    [hRC : ∀ l bw, Persistent (RC l bw)] (MP : GoInterface → IProp netDistGF)
    (wp_Recall : hook.ocf.OptCondF.Recall.specI)
    (str0 : swift.CommandId → GoString)
    (wp_String0 : swift.CommandId.String.specS str0)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_Leader : replica.Leader.spec)
    (wp_newFA : swift.newFastAck.specP)
    (wp_copyFA : swift.copyFastAck.specP)
    (wp_deliver0 : ∀ γdl, swift.Replica.deliver.specE str0 γdl MP)
    (wp_hfa0 : ∀ c : swift.DC, c.str = str0 → swift.Replica.handleFastAck.specIc RC MP swift.ackCtx c)
    (wp_SFA : swift.Batcher.SendFastAck.specI (hG := hG))
    (wp_SFAC : swift.Batcher.SendFastAckClient.specI (hG := hG)) :
    ∀ c : swift.DC, c.str = str0 → RC = swift.RCh c.γ c.γc c.γm c.rp →
      swift.Replica.handlePropose.specIc RC MP swift.proposeCtx c := by
  intro c hc hRCe γd d x b Do pm gp cc dep hs sq ld s B D P H
  have wp_String : ∀ _c : swift.DC, swift.CommandId.String.specS c.str := fun _ => hc ▸ wp_String0
  have wp_deliver : ∀ _c : swift.DC, swift.Replica.deliver.specE c.str c.γdl MP :=
    fun _ => hc ▸ wp_deliver0 c.γdl
  have wp_hfa : ∀ _c : swift.DC, swift.Replica.handleFastAck.specIc RC MP swift.ackCtx c :=
    fun _ => wp_hfa0 c hc
  wp_start as ⟨#Hctx, #Hac, Hown, Hm, Hnt⟩
  iunfold swift.propMsgR at Hm
  icases Hm with ⟨#Hpm, #Hhalf, #Hdep, #Hhs, %Hnn, #Hfacts, #Hnum⟩
  ihave #Hpm2 := Hpm
  iStructNamedPrefix Hpm2 "PM"
  iunfold swift.descOwnF at Hown
  icases Hown with ⟨Hown, Hocf⟩
  iunfold swift.descOwn at Hown
  icases Hown with ⟨%msS, %msF, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF,
    HdS, HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, ⟨#Hra, -⟩, %Hph,
    #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HdF, ⟨Hcore, ⟨Hrest, HDo⟩⟩⟩⟩
  -- round 47 (46-2): a set proposal holds `x`'s row token (`rowTokO`), whose key the message's
  -- fresh claim also claims: impossible (`claim_rowTok_false`), so `propose` is nil here
  by_cases hpn0 : dv.propose = null
  rotate_left
  · iunfold swift.rowTokO at Htok
    icases Htok with (⟨Htk, -⟩ | ⟨%Hn, -, -⟩)
    rotate_left
    · exact absurd Hn.2 hpn0
    ihave #Hctx4 := Hctx
    iunfold swift.DC.ctx at Hctx4
    iunfold swift.descCtxE at Hctx4
    icases Hctx4 with ⟨%me4, %fr4, %lg4, %dm4, %dc4, %ex4, %dr4, %oe4, %γa4, %γrm4, %rc4, %γrc4, -, -, -,
      -, -, -, -, -, #Hninv4, -⟩
    iapply fupd_wp
    imod (swift.claim_rowTok_false c.γ c.γv c.γe c.γo c.sn c.k (b, toCmdId x) .fresh rv)
      $$ [Hninv4 Hnt Htk] with Hf
    · iframe Hninv4 Hnt Htk
    iexfalso; iexact Hf
  ihave ⟨%st, %fq, %szF', %memF', Hst, HFQ, #HqF, %HAQ, Henv, Hshb⟩ := swift.shOwn_openE c d b qe $$ Hsh
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph', Hcmd, #Hvs, Hdep, #HD, Hhs1, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
  iunfold swift.descRest at Hrest
  icases Hrest with ⟨%pd, %hs0, %sq0, %df, Hpd, Hsq, Hhs0, Hdf, #Hpdok⟩
  icombine Hhs1 Hhs0 gives %Hhe
  subst Hhe
  ihave Hhsf := (swift.pt_halves (swift.dfld d go!"hs") dv.hs).2 $$ [Hhs1 Hhs0]
  · iframe Hhs1 Hhs0
  wp_auto
  rw [decide_eq_false Hnn.1]
  wp_auto
  -- P4 prefix: `proposeDep` (and `hs`, `seqnum`) set by the first proposal message
  wp_join iprop(∃ (pd' hs' : GoSlice) (sq' : w64),
      swift.dfld d go!"proposeDep" ↦ pd' ∗ swift.dfld d go!"seqnum" ↦ sq' ∗
      swift.dfld d go!"hs" ↦ hs' ∗ (∃ Hs' : List swift.SHash, hs' ↦*□ Hs') ∗
      swift.pdOk c b x pd' hs' sq' ∗ ⌜pd' ≠ slice.nil⌝ ∗ desc_ptr ↦ d ∗ pm_ptr ↦ pm)
    with [Hpd Hsq Hhsf desc pm]
    as ⟨%pd', %hs', %sq', Hpd, Hsq, Hhsf, ⟨%Hs', #HHs'⟩, #Hpdok', %Hpdnn, desc, pm⟩
  · rw [decide_eq_false Hnn.2]
    wp_auto
    wp_join_done
    iexists dep, hs, sq
    iframe Hpd Hsq Hhsf
    isplitr
    · iexists [H]; iexact Hhs
    isplitr
    · iunfold swift.pdOk
      iright; ileft
      iexists cc, ld, s, B, D, P, H
      iframe Hdep Hhs Hfacts Hnum
      ipureintro; exact Hnn.1
    iframe desc pm
    ipureintro; exact Hnn.1
  · -- the first writer's `proposeDep` stays (a proposal's or, G15, a sync entry's)
    ihave #Hpdok0 := Hpdok
    iunfold swift.pdOk at Hpdok0
    icases Hpdok0 with (%Hn | #Hpp)
    · exfalso; exact Hif Hn.1
    iexists pd, dv.hs, sq0
    iframe Hpd Hsq Hhsf
    isplitr
    · iexists dv.Hs; iexact HHs
    iframe Hpdok desc pm
    ipureintro; exact Hif
  icases (swift.pt_halves (swift.dfld d go!"hs") hs').1 $$ Hhsf with ⟨Hhs, Hhs0⟩
  try wp_auto
  -- `r.status != NORMAL || desc.propose != nil`: return, the owner state as it is
  by_cases hst : st = W64 0
  rotate_left
  · rw [decide_eq_false hst]
    wp_auto
    iapply HΦ
    ileft
    iunfold swift.descOwnF
    iframe Hocf
    refoldHP1
  rw [decide_eq_true hst]
  wp_auto
  have hp0 : dv.propose = null := hpn0
  rw [decide_eq_true hp0]
  wp_auto
  -- `desc.propose = msg; desc.cmd = msg.Command`: both halves of `propose`
  iunfold swift.descOcf at Hocf
  icases Hocf with ⟨%cf, %cond, %fs, %v, Hocfr, #Hcond, #Hvf, #Hfs⟩
  iunfold swift.ocfRes at Hocfr
  icases Hocfr with ⟨Hapf, Hocf, HPc, %sb, %bs, Hsb, Hbs, Hbsc, %Hb⟩
  iunfold swift.proposeHalf at HPc
  icases HPc with ⟨%p1, Hp1, %Hpv⟩
  icombine Hprop Hp1 gives %Hpe
  subst Hpe
  -- round 28 (G7/G10): the row token arrives with the proposal (`install_tok`)
  iclear Hra Hcom
  iapply fupd_wp
  ihave #Htl : swift.takeLaw c $$ [Hac]
  · iunfold swift.proposeCtx at Hac; icases Hac with ⟨-, #Htl, -⟩; iexact Htl
  imod (swift.install_tok c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) dv rv qe bw stp rcp
      fs) $$ [Hrd Htok Hnt Henv] with ⟨Hrd, Henv, Htok, Hslt, %Hcl0, #Hfs2⟩
  · iframe Hctx Htl Hrd Htok Hnt Hfs Henv
  imodintro
  -- G15 (round 30): a sync entry's `proposeDep` (its `sp.accepted`) against the fresh token's
  -- row (not accepted): refuted; the proposal's facts remain (`Hpdx`)
  ihave #Hpdx := Hpdok'
  iunfold swift.pdOk at Hpdx
  icases Hpdx with (%Hn0 | #Hpdx | ⟨%Ds, %Hn0, #HDs, #Hacc, -⟩)
  · exfalso; exact Hpdnn Hn0.1
  rotate_left
  · ihave #Hctx3 := Hctx
    iunfold swift.DC.ctx at Hctx3
    iunfold swift.descCtxE at Hctx3
    icases Hctx3 with ⟨%me3, %fr3, %lg3, %dm3, %dc3, %ex3, %dr3, %oe3, %γa3, %γrm3, %rc3, %γrc3, -, -,
      %Hids3, -, -, -, #Hinv3, #Hcfg3, #Hninv3, -⟩
    obtain ⟨-, -, hrN3, -, -, hk3⟩ := Hids3
    iunfold swift.epochRd at Hrd
    icases Hrd with ⟨-, -, -, Het, -, -⟩
    iapply fupd_wp
    imod (swift.accepted_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr3 lg3 qe b (toCmdId x)
        swift.rowEmpty hrN3 hk3) $$ [Het Htok] with ⟨-, -, %Hacc1⟩
    · iframe Hinv3 Hcfg3 Hninv3 Het Htok Hacc
    exfalso; simp [swift.rowEmpty] at Hacc1
  ihave Hpf := (swift.pt_halves (swift.dfld d go!"propose") dv.propose).2 $$ [Hprop Hp1]
  · iframe Hprop Hp1
  ihave #HpI := Hhalf
  iunfold swift.propIs at Hhalf
  icases Hhalf with ⟨%pp, %w, %mu, %addr, %ts, %vs, #Hgp, #Hpx, #Hvs2, #Hcis, %Hpp⟩
  ihave #Hpx2 := Hpx
  iStructNamedPrefix Hpx2 "PX"
  ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
  ihave #Hgp2 := Hgp
  iStructNamedPrefix Hgp2 "G"
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep, %Hids,
    -, -, #Hoe, #Hinv, #Hcfg, #Hninv, #Hdm, #Hcm, #HdI, -⟩
  iapply fupd_wp
  ihave Hcok := sp.cmdIs_ok (γ := c.γ) (γc := c.γc) (γm := c.γm) (γl := c.γl) (toCmdId x) cc
    $$ [Hinv Hcis]
  · iframe Hinv Hcis
  imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hcok with %Hcok
  imodintro
  have hcl : (toCmdId x).cl ≠ -1 := by
    intro h; have := Hcok.2.1; rw [h] at this; exact absurd this (by decide)
  -- round 47 (46-2): `x`'s client id, read-only (`replyPre`)
  ihave #HclId : typedPointsto (pp.[replica.defs.Propose, go!"ClientId"]) x.ClientId' DFrac.discard
    $$ [PXClientId]
  · iExactEq PXClientId; rfl
  have Hcop : cc.op ≠ W8 3 := by
    rcases Hcok.1 with h | h
    · unfold sp.Cmd.isPut sp.opPUT at h; simp at h; rw [h]; decide
    · unfold sp.Cmd.isGet sp.opGET at h; simp at h; rw [h]; decide
  -- L2 (item 4): `if desc.phase == COMMIT { ghostCommit(r.ballot, cmdId) }`, the deferred commit
  -- (unreachable in Go, nonissues/e1; the proof's invariant allows it at the leader)
  try wp_auto
  wp_join iprop(∃ rv : swift.RowV, swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp ∗
      swift.rowTok c.γo b (toCmdId x) rv ∗
      (⌜rv.2.2.2 = false⌝ ∨ sp.committed c.γ c.r b (toCmdId x)) ∗
      ⌜rv.1 = none ∧ rv.2.1 = none ∧ rv.2.2.1 = false ∧
        (dv.phase = swift.phCOMMIT → rv.2.2.2 = true) ∧
        (rv.2.2.2 = true → dv.phase = swift.phCOMMIT ∧ c.r = sp.leaderOf c.N b)⌝ ∗
      r_ptr ↦ c.rp ∗ cmdId_ptr ↦ x)
    with [Hrd Htok r cmdId] as ⟨%rv, Hrd, Htok, #Hcom, %Hrv4, r, cmdId⟩
  · have hc : dv.phase = swift.phCOMMIT := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif) | simpa using Hif
    ihave #Hctx4 := Hctx
    iunfold swift.DC.ctx at Hctx4
    iunfold swift.descCtxE at Hctx4
    icases Hctx4 with ⟨%me4, %fr4, %lg4, %dm4, %dc4, %ex4, %dr4, %oe4, %γa4, %γrm4, %rc4, %γrc4, -, -,
      %Hids4, -, -, -, #Hinv4, #Hcfg4, #Hninv4, -⟩
    obtain ⟨-, -, hrN4, -, -, hk4⟩ := Hids4
    iunfold swift.epochRd at Hrd
    icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
    try wp_auto
    ihave #Hng := swift.DC.ctx_ng c $$ Hctx
    ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
    · iPkgInit
    try wp_auto
    wp_bind (App (App (Val (@! swift.resolveCommit)) (Val _)) (Val _))
    iapply (swift.wp_resolveCommit c.γ c.k _ x iprop(swift.epochTok c.γe qe (b, b) ∗
      swift.rowTok c.γo b (toCmdId x) (swift.rowEmpty.1, swift.rowEmpty.2.1, swift.rowEmpty.2.2.1, true) ∗
      sp.committed c.γ c.r b (toCmdId x))) $$ [Het Htok]
    · iframe #
      isplitr
      · ipureintro; exact Hbw.2
      iunfold swift.resolveUpd
      iintro %W' Hpp
      rw [Hbw.1]
      imod (swift.commit_dstep' (⊤ \ ↑client.nodeProphN) swift.nodeN_pE swift.spN_pE c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr4 lg4 qe b
          (toCmdId x) swift.rowEmpty hrN4 hk4 rfl W') $$ [Het Htok Hpp] with ⟨Het, Htok, Hpost, #Hc⟩
      · iframe Hinv4 Hcfg4 Hninv4 Het Htok Hpp
        ileft; ipureintro; exact Hcl0 hc
      imodintro
      iframe Hpost Het Htok Hc
    inext
    iintro ⟨Het, Htok, #Hc⟩
    try wp_auto
    wp_join_done
    iexists _
    iframe Htok r cmdId
    isplitl [Hbal HStf Hrcf Het Hxe]
    · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
    isplitr
    · iright; iexact Hc
    ipureintro
    exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => ⟨hc, Hcl0 hc⟩⟩
  · have hnc : ¬ dv.phase = swift.phCOMMIT := by
      first | exact Hif | exact fun h => absurd (go.intoVal_inj Hif) (by simp [h]) | simpa using Hif
    try wp_auto
    try wp_join_done
    iexists swift.rowEmpty
    iframe Hrd Htok r cmdId
    isplitr
    · ileft; ipureintro; rfl
    ipureintro
    exact ⟨rfl, rfl, rfl, fun h => absurd h hnc, fun h => by simp [swift.rowEmpty] at h⟩
  have Hph : dv.phase = swift.phCOMMIT → rv.2.2.2 = true ∨ dv.propose = null :=
    fun h => Or.inl (Hrv4.2.2.2.1 h)
  -- round B1 (D81): not `rowAcc` at the proposal-less values (the fresh row may be committed, at
  -- the leader); its accepted part, and the row's empty pre-acceptance and path (`Hrv4`)
  ihave #Hra1 : iprop(⌜rv.2.2.1 = false⌝ ∨ sp.accepted c.γ c.r b (toCmdId x)) $$ []
  · ileft; ipureintro; exact Hrv4.2.2.1
  try wp_auto
  -- `r.FQ.Contains(r.Id)`
  ihave #HN := Hrep
  iunfold replica.isReplica at HN
  icases HN with ⟨%lg', %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #Hid, -⟩
  iunfold swift.descCore at Hcore
  icases Hcore with ⟨%wa, %sl, Hwa, Hsl, #Hw⟩
  ihave %Hfq := replica.mset.quorumIs_ok $$ HqF
  obtain ⟨iF, rfl⟩ := Hfq
  wp_auto
  wp_apply (swift.wp_qContainsIff iF szF' memF' me) $$ [$HqF] as %fast %Hfast
  icases (swift.pt_halves (swift.dfld d go!"propose") gp).1 $$ Hpf with ⟨Hprop, Hp1⟩
  ihave Hcore : swift.descCore c d x b $$ [Hwa Hsl]
  · iunfold swift.descCore; iexists wa, sl; iframe Hwa Hsl
    iexact Hw
  cases fast
  · -- outside the fast quorum: the stored closures run (`Recall`), return
    -- round 47 (46-2): the reply facts (a follower: E7 below); the hash is the first proposal
    -- message's (`pdOk`)
    have hnl0 : c.r ≠ sp.leaderOf c.N b := fun h => by
      have := Hfast.2 (HAQ.2 me Hids.2.1 (by rw [Hids.1]; exact h)); cases this
    ihave #HpdxA := Hpdx
    icases HpdxA with ⟨%ccA, %ldA, %sA, %BA, %DA, %PA, %HA, -, -, #HhA, #HfA, -⟩
    iunfold swift.propFacts at HfA
    icases HfA with ⟨-, -, #HshA, %HpfA⟩
    ihave %HsEqA := ownSlice_agree hs' _ _ Hs' [HA] $$ HHs' HhA
    ihave #HrPa := swift.repPre_prop c.γ c.N c.r b x
      ({ dv with propose := gp, c := cc, vs := vs, hs := hs', Hs := Hs' } : swift.DescV)
      pp w mu addr HA PA sA HsEqA Hpp.1
      (by show dv.D.length < 2 ^ 62; rw [(Hrp.1.1 hp0).2]; decide) HpfA.2.2.2.1 hcl
      (fun h => absurd h hnl0) $$ [Hgp HclId HshA HpI]
    · iframe Hgp HclId HshA HpI; ileft; ipureintro; exact hnl0
    restHP
    ihave Hsh := Hshb $$ Hst HFQ Henv
    ihave Hown : swift.descOwn c RC MP γd d x b
        iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do))
        $$ [HdS Hrd Hsh HRC Htok Hslt Hcom HsF HfF HdF Hcore HDo Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs]
    · iunfold swift.descOwn
      iexists msS, msF, qS, qF, szS, szF, memS, memF, hd
      iframe HhS HhF HdS
      iunfold swift.setR
      iunfold swift.descSt
      iexists qe, bw, stp, rcp, { dv with propose := gp, c := cc, vs := vs, hs := hs', Hs := Hs' }, rv
      ihave Htok := swift.rowTokO_of2 c b x
        { dv with propose := gp, c := cc, vs := vs, hs := hs', Hs := Hs' } rv $$ Htok Hslt
      simp only [ite_true, if_true, ↓reduceIte]
      iframe Hsh Hrd HRC Htok Hcom HsB HsF HfF HdF Hcore HDo
      -- E7 (table rev 3-5): outside `FQ`, so not `b`'s leader (the leader is in `FQ`)
      have hnl : c.r ≠ sp.leaderOf c.N b := fun h => by
        have := Hfast.2 (HAQ.2 me Hids.2.1 (by rw [Hids.1]; exact h)); cases this
      have hph03 := Hrp.1.1 hp0
      isplitl [Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs]
      · iunfold swift.descF; iframe Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs2 HD HHs' Hmb HsL
        ipureintro; exact Hcop
      isplitr
      · isplitr
        · iunfold swift.rowAcc
          iframe Hra1; isplitr
          · ipureintro; intro _; exact Hgpnn
          iright; iexists _; iexact Hgp
        iexact HrPa
      isplitr
      · ipureintro; exact fun h => Or.inl (Hrv4.2.2.2.1 h)
      isplitr
      · iapply swift.phaseWhy_ne1
        show dv.phase ≠ W64 1
        rcases hph03.1 with h | h <;> rw [h] <;> decide
      isplitr
      · -- round 54: at `START` the trivial disjunct. R55 (54-1, D77 (2)): `COMMIT` without a
        -- proposal before is refuted by the fresh token's row (`install_tok`: a committed row only
        -- at the leader), so `rowPhaseOk` needs no tightening here
        rcases hph03.1 with h0 | h3
        · iunfold swift.depWhy; ileft; ileft; ipureintro; right; right; exact h0
        · exfalso
          exact hnl (Hrv4.2.2.2.2 (Hrv4.2.2.2.1 (by rw [h3]; rfl))).2
      ipureintro
      refine ⟨swift.rowPhaseOk_prop c.N c.r b _ rv Hgpnn hph03.1 hph03.2 (fun _ => hnl) Hrv4.1
        Hrv4.2.2.1 (fun h => (Hrv4.2.2.2.2 h).1), Hrp.2⟩
    wp_auto
    ihave HPc : swift.proposeHalf d true $$ [Hp1]
    · iunfold swift.proposeHalf; iexists gp; iframe Hp1; ipureintro; simp [Hgpnn]
    by_cases hfs : fs.isEmpty = true
    · -- nothing stored: `Recall` does nothing
      wp_apply (wp_Recall cf cond fs (swift.proposeHalf d) true iprop(True)) $$ [Hocf HPc]
        as %rb ⟨%Hrb, Hres⟩
      · iframe Hocf Hcond HPc
        simp only [hfs, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        itrivial
      simp only [hfs, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      icases Hres with ⟨Hocf, HPc⟩
      iapply HΦ
      ileft
      iunfold swift.descOwnF
      iframe Hown
      iunfold swift.descOcf
      iexists cf, cond, fs, true
      iframe Hcond Hfs
      isplitl [Hapf Hocf HPc Hsb Hbs Hbsc]
      · iunfold swift.ocfRes; iframe Hapf Hocf HPc
        iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact Hb
      have : fs = [] := by simpa using hfs
      subst this
      iapply swift.ocfV_nil
    · -- the stored closures run (`chain`), the store is empty after
      let Q : IProp netDistGF := iprop((swift.descOwnF c RC MP γd d x b
          iprop(swift.descRest c b x d ∗ Do) ∨ swift.descDone c b x d))
      wp_apply (wp_Recall cf cond fs (swift.proposeHalf d) true Q)
        $$ [Hocf HPc Hown Hapf Hsb Hbs Hbsc] as %rb ⟨%Hrb, Hres⟩
      · iframe Hocf Hcond HPc
        simp only [hfs, Bool.not_false, Bool.and_true, ↓reduceIte]
        iintro HPc Hocf
        ihave Ho : swift.ocfRes0 d $$ [Hapf Hocf HPc Hsb Hbs Hbsc]
        · iunfold swift.ocfRes0; iexists cf, cond; iframe Hcond
          iunfold swift.ocfRes; iframe Hapf Hocf HPc
          iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact ⟨Hb.1, by simp⟩
        iapply (swift.recall_chain c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) Q fs)
          $$ Hfs2 [Hown Ho]
        · iframe Hown Ho
        iintro Hst
        icases Hst with (⟨Hown, Ho⟩ | Hdone)
        · ileft
          iunfold swift.descOwnF
          iframe Hown
          iunfold swift.ocfRes0 at Ho
          icases Ho with ⟨%cf', %cond', Ho, #Hcond'⟩
          iunfold swift.descOcf
          iexists cf', cond', [], true
          iframe Ho Hcond'
          isplitr
          · iapply swift.ocfV_nil
          iapply BigSepL.bigSepL_nil.2; itrivial
        · iright; iexact Hdone
      simp only [hfs, Bool.not_false, Bool.and_true, ↓reduceIte]
      iapply HΦ
      iexact Hres
  -- in the fast quorum: `desc.dep = desc.proposeDep; desc.phase = PRE_ACCEPT`, pre-accepted
  have hAQ : c.r ∈ sp.AQ c.N b := by
    have := HAQ.1 me (Hfast.1 rfl); rw [Hids.1] at this; exact this
  ihave #Hpdok2 := Hpdok'
  icases Hpdx with ⟨%cc0, %ld0, %s0, %B0, %D0, %P0, %H0, %Hn, #Hd0, #Hh0, #Hf0, #Hq0⟩
  iunfold swift.propFacts at Hf0
  icases Hf0 with ⟨#Hlb0, #HB0, #Hsh0, %Hpf0⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := Hpf0
  obtain ⟨hy, hD, hB, hLP, hP⟩ := swift.propFacts_pre s0 B0 D0 P0 (toCmdId x) cc0 ld0 c.N c.r b
    g1 g2 g3 g4 g5 g6 g7 g8
  have hrv : rv.1 = none ∧ rv.2.1 = none := ⟨Hrv4.1, Hrv4.2.1⟩
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  wp_auto
  -- L2 (item 4): the pre-acceptance at its resolution, `ghostPreaccept(r.ballot, cmdId, desc.dep)`
  ihave #Hng := swift.DC.ctx_ng c $$ Hctx
  ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
    pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
  · iPkgInit
  wp_bind (App (App (App (Val (@! swift.resolvePreaccept)) (Val _)) (Val _)) (Val _))
  iapply (swift.wp_resolvePreaccept c.γ c.k _ x _ (D0.map ofCmdId)
    iprop(swift.epochTok c.γe qe (b, b) ∗
      swift.rowTok c.γo b (toCmdId x) (some D0, some P0, rv.2.2) ∗
      sp.preacc c.γ c.r b (toCmdId x) D0 ∗ sp.pathIs c.γ c.r b (toCmdId x) P0)) $$ [Het Htok]
  · iframe #
    isplitr
    · ipureintro; exact Hbw.2
    iunfold swift.resolveUpd
    iintro %W' Hpp
    rw [Hbw.1, List.map_map, show toCmdId ∘ ofCmdId = id from rfl, List.map_id]
    imod (swift.preaccept_dstep (⊤ \ ↑client.nodeProphN) swift.nodeN_pE swift.spN_pE c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
        (toCmdId x) s0 B0 D0 P0 rv Hids.2.2.1 Hids.2.2.2.2.2 hAQ hy hD hB g4 hLP hP hrv W')
      $$ [Het Htok Hpp] with ⟨Het, Htok, Hpost, #Hpre, #Hpath⟩
    · iframe Hinv Hcfg Hninv Het Htok Hlb0 HB0 Hpp
    imodintro
    iframe Hpost Het Htok Hpre Hpath
  inext
  iintro ⟨-, Het, Htok, #Hpre, #Hpath⟩
  try wp_auto
  iapply fupd_wp
  -- round 47 (46-2): the dependencies are few (`replyPre`), from the sequence's small ids
  ihave Hsm0 := swift.locLb_small (γ := c.γ) (γc := c.γc) (γm := c.γm) (γl := c.γl) c.r b s0
    $$ [Hinv Hlb0]
  · iframe Hinv Hlb0
  imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hsm0 with %Hsm0
  imodintro
  have hlen00 : s0.length ≤ 6 * 2 ^ 32 := by
    have := swift.small_ids_len (s0.map Prod.fst) g9 (by
      intro y hy; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy; exact Hsm0 p hp)
    simpa using this
  obtain ⟨hDw0, -⟩ := swift.propDeps_wf s0 (toCmdId x) cc0 D0 hlen00 g2 g3
  -- round 47 (46-2): the reply facts: the message's hash, and at the leader its path and
  -- sequence (`x` last, its dependencies `depsIn`; the command is the registered one)
  ihave %HsEq0 := ownSlice_agree hs' _ _ Hs' [H0] $$ HHs' Hh0
  ihave %Hcc := swift.locLb_cmd_agree c.γ c.r b s0 (toCmdId x) cc cc0 (List.mem_of_getLast? g1)
    $$ [Hlb0 Hcis]
  · iframe Hlb0 Hcis
  ihave #HrPa := swift.repPre_prop c.γ c.N c.r b x
    ({ dv with propose := gp, c := cc, vs := vs, hs := hs', Hs := Hs', dep := pd', D := D0.map ofCmdId, phase := W64 1 } : swift.DescV)
    pp w mu addr H0 P0 s0 HsEq0 Hpp.1
    (by show (D0.map ofCmdId).length < 2 ^ 62; rw [List.length_map]; exact hDw0) g4 hcl
    (fun _ => ⟨by show (toCmdId x, cc) ∈ s0; rw [Hcc]; exact List.mem_of_getLast? g1,
      by show ((D0.map ofCmdId).map toCmdId).Perm (sp.depsIn s0 (toCmdId x))
         rw [show (D0.map ofCmdId).map toCmdId = D0 by simp [List.map_map, Function.comp_def]]
         exact List.Perm.of_eq hD⟩)
    $$ [Hgp HclId Hsh0 Hpath Hlb0 HpI]
  · iframe Hgp HclId Hsh0 HpI; iright; iframe Hpath Hlb0
  -- the owner state with the pre-acceptance, then `Recall` (P5: the ack's fields read before)
  ihave HDo : iprop(swift.descRest c b x d ∗ Do) $$ [Hpd Hsq Hhs0 Hdf HDo]
  · iframe HDo; iunfold swift.descRest; iexists pd', hs', sq', df
    iframe Hpd Hsq Hhs0 Hdf Hpdok2
  have hDD : (D0.map ofCmdId).map toCmdId = D0 := by simp [List.map_map, Function.comp_def]
  ihave #Hpre2 : sp.preacc c.γ c.r b (toCmdId x) ((D0.map ofCmdId).map toCmdId) $$ [Hpre]
  · rw [hDD]; iexact Hpre
  ihave Hsh := Hshb $$ Hst HFQ Henv
  ihave Hown : swift.descOwn c RC MP γd d x b
      iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do))
      $$ [HdS Hsh Hbal HStf Hrcf Het Hxe HRC Htok Hslt Hcom HsF HfF HdF Hcore HDo Hph' Hcmd Hdep Hhs
        Hprop Hseq Hmsgs]
  · iunfold swift.descOwn
    iexists msS, msF, qS, qF, szS, szF, memS, memF, hd
    iframe HhS HhF HdS
    iunfold swift.setR
    iunfold swift.descSt
    iexists qe, bw, stp, rcp, ({ dv with propose := gp, c := cc, vs := vs, hs := hs', Hs := Hs', dep := pd', D := D0.map ofCmdId, phase := W64 1 } : swift.DescV), ((some D0, some P0, rv.2.2) : swift.RowV)
    simp only [if_true, ↓reduceIte]
    ihave Htok := swift.rowTokO_of2 c b x ({ dv with propose := gp, c := cc, vs := vs, hs := hs', Hs := Hs', dep := pd', D := D0.map ofCmdId, phase := W64 1 } : swift.DescV) ((some D0, some P0, rv.2.2) : swift.RowV) $$ Htok Hslt
    iframe Hsh HRC Htok Hcom HsB HsF HfF HdF Hcore HDo
    isplitl [Hbal HStf Hrcf Het Hxe]
    · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
    isplitl [Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs]
    · iunfold swift.descF; iframe Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs2 Hd0 HHs' Hmb HsL
      ipureintro; exact Hcop
    isplitr
    · isplitr
      · iunfold swift.rowAcc; iframe Hra1; isplitr
        · ipureintro; intro _; exact Hgpnn
        iright; iexists _; iexact Hgp
      iexact HrPa
    isplitr
    · ipureintro; intro h; simp [swift.phCOMMIT] at h
    isplitr
    · iunfold swift.phaseWhy; iright; iexact Hpre2
    isplitr
    · iunfold swift.depWhy; iright; ileft
      isplitr
      · ipureintro; exact Or.inr (show uint.nat (W64 1) ≤ 1 by decide)
      iexact Hpre2
    ipureintro
    refine ⟨swift.rowPhaseOk_pre c.N c.r b _ _ Hgpnn rfl (by show some D0 = some _; rw [hDD])
      Hrv4.2.2.1 (fun h => (Hrv4.2.2.2.2 h).2), Hrp.2⟩
  wp_apply (swift.wp_recallP wp_Recall c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) cf cond
      fs gp Hgpnn) $$ [Hocf Hp1 Hown Hapf Hsb Hbs Hbsc]
    as %rb Hst
  · iframe Hocf Hcond Hp1 Hfs2 Hown Hapf
    iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact Hb.1
  -- `r.delivered.Has(cmdId.String()) || (recalled && desc.slowPath)`: return
  icases Hst with (⟨Hown, Ho⟩ | ⟨Hdone, %Hrb⟩)
  rotate_left
  · -- a closure retired the descriptor: `x` is in `delivered`
    iunfold swift.descDone at Hdone
    icases Hdone with Hgone
    iunfold swift.descGone at Hgone
    icases Hgone with ⟨%Hsq, #Hex, Hret, %qe', %bw', %stp', %rcp', Hrd', Hsh'⟩
    ihave ⟨HrdR, Hpin, Hshr⟩ := swift.shOwnR_rdrP c d b qe' $$ Hsh'
    hasGoneP qe'
    ihave Hsh' := Hshr $$ HrdR Hpin
    wp_auto
    iapply HΦ
    iright
    iunfold swift.descDone
    iunfold swift.descGone
    iframe Hex Hret
    isplitr
    · ipureintro; exact Hsq
    iexists qe', bw', stp', rcp'; iframe Hrd' Hsh'
  iunfold swift.ocfRes0 at Ho
  icases Ho with ⟨%cf, %cond, Ho, #Hcond⟩
  iunfold swift.ocfRes at Ho
  icases Ho with ⟨Hapf, Hocf, HPc, %sb, %bs, Hsb, Hbs, Hbsc, %Hb⟩
  ihave ⟨HrdR, Hownr⟩ := swift.descOwn_rdr _ _ _ _ _ _ _ _ $$ Hown
  hasAnyP
  ihave Hown := Hownr $$ HrdR
  cases dl
  rotate_left
  · wp_auto
    exitOwnP
  wp_auto
  ihave ⟨%sl0, Hsl0, Hslb⟩ := swift.descOwn_slowPath c RC MP γd d x b
    iprop(swift.descRest c b x d ∗ Do) $$ Hown
  wp_bind (If (Val _) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(rb && sl0)⌝ ∗ swift.dfld d go!"slowPath" ↦ sl0 ∗
    desc_ptr ↦ d)))
    $$ [Hsl0 desc]
  · cases rb
    · wp_auto; iframe; ipureintro; rfl
    · wp_auto; iframe; ipureintro; rfl
  iintro %v ⟨%Hv, Hsl0, desc⟩
  subst Hv
  ihave Hown := Hslb $$ Hsl0
  by_cases hrs : (rb && sl0) = true
  · rw [hrs]
    wp_auto
    exitOwnP
  rw [Bool.not_eq_true] at hrs
  rw [hrs]
  wp_auto
  -- N2-nofast (fork 66dfc21): `recalled && desc.waitingAck != nil && r.Id != r.leader()`:
  -- return. Either branch is a safe exit or the old path: the condition is read under the
  -- owner state (`waitingAck` from `descCore`, the ballot for `leader()`) and given back.
  have hN0 : 1 ≤ c.N ∧ c.N ≤ 7 := ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩
  wp_bind (If (If (Val _) _ _) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜∃ bb : Bool, v = #bb⌝ ∗
      swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do)) ∗
      desc_ptr ↦ d ∗ r_ptr ↦ c.rp)))
    $$ [Hown desc r]
  · ihave ⟨%wa, Hwa, -, Hwab⟩ := swift.descOwn_waiting c RC MP γd d x b
      iprop(swift.descRest c b x d ∗ Do) $$ Hown
    wp_bind (If (Val _) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜∃ bb : Bool, v = #bb⌝ ∗
        swift.dfld d go!"waitingAck" ↦ wa ∗ desc_ptr ↦ d)))
      $$ [Hwa desc]
    · cases rb
      · wp_auto; iframe; ipureintro; exact ⟨false, rfl⟩
      · wp_auto; iframe; ipureintro; exact ⟨_, rfl⟩
    iintro %v ⟨%Hv, Hwa, desc⟩
    obtain ⟨bb, rfl⟩ := Hv
    ihave Hown := Hwab $$ Hwa
    cases bb
    · wp_auto; iframe; ipureintro; exact ⟨false, rfl⟩
    · ihave ⟨%qe1, %bw1, Hbal1, %Hbw1, Hbalb1⟩ := swift.descOwn_ballot c RC MP γd d x b _ $$ Hown
      wp_auto
      wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw1 _ c.N hN0) $$ [$Hbal1 $Hrr $HN]
        as Hbal1
      ihave Hown := Hbalb1 $$ Hbal1
      iframe; ipureintro; exact ⟨_, rfl⟩
  iintro %v ⟨%Hv, Hown, desc, r⟩
  obtain ⟨bb, rfl⟩ := Hv
  cases bb
  rotate_left
  · wp_auto
    exitOwnP
  wp_auto
  -- `r.slowAddrs[msg.Addr]`: empty
  ihave #Hac2 := Hac
  iunfold swift.proposeCtx at Hac2
  icases Hac2 with ⟨#Hack, -, %sam, %frR, %lgR, %vP, #Hsam, #Hsamm, #HfrR, #HcfgR, #HvP⟩
  wp_auto
  wp_apply (wp_map_lookup2 go.string (go.StructType []) sam (∅ : GMap GoString Unit) addr
    DFrac.discard) $$ [$Hsamm] as -
  -- the new fast ack
  wp_apply (wp_newFA vP) $$ [$HvP] as %la ⟨%fa0, Hla⟩
  ihave ⟨%qe2, %bw2, Hbal2, %Hbw2, Hbalb⟩ := swift.descOwn_ballot c RC MP γd d x b _ $$ Hown
  have hN : 1 ≤ c.N ∧ c.N ≤ 7 := ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩
  wp_auto
  wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw2 _ c.N hN) $$ [$Hbal2 $Hrr $HN] as Hbal2
  wp_join iprop(∃ sqv : w64, la ↦ swift.MFastAck.mk me bw2 x pd' hs' sqv ∗ fastAck_ptr ↦ la ∗
      ackSeq_ptr ↦ sq' ∗
      ⌜me = BitVec.srem bw2 (W32 (sint.Z (W64 (c.N : Int)))) → sqv = sq'⌝)
    with [Hla fastAck ackSeq] as ⟨%sqv, Hla, fastAck, ackSeq, %Hsqv⟩
  any_goals (iexists sq'; iframe; ipureintro; intro _; rfl)
  any_goals (iexists _; iframe; ipureintro; intro h; exact absurd h Hif)
  ipersist Hla
  -- `isRead := r.fastRead && msg.Command.Op != PUT`
  wp_bind (If (Val _) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(frR && !cc.isPut)⌝ ∗ msg_ptr ↦ gp)))
    $$ [msg]
  · cases frR
    · wp_auto; iframe; ipureintro; rfl
    · ihave #HCmd := PXCommand
      iStructNamedPrefix HCmd "K"
      wp_auto
      iframe msg
      ipureintro
      simp only [sp.Cmd.isPut, sp.opPUT, Bool.true_and]
      rfl
  iintro %v ⟨%Hv, msg⟩
  subst Hv
  wp_auto
  wp_apply (wp_copyFA vP la _) $$ [$HvP $Hla] as %la2 Hla2
  -- the fast ack's model and witness (`f.wf`: GAP SWB-13 closed by the ids' bound)
  iapply fupd_wp
  ihave Hsm := swift.locLb_small (γ := c.γ) (γc := c.γc) (γm := c.γm) (γl := c.γl) c.r b s0
    $$ [Hinv Hlb0]
  · iframe Hinv Hlb0
  imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hsm with %Hsm
  imodintro
  have hlen0 : s0.length ≤ 6 * 2 ^ 32 := by
    have := swift.small_ids_len (s0.map Prod.fst) g9 (by
      intro y hy; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy; exact Hsm p hp)
    simpa using this
  obtain ⟨hDw, hDne⟩ := swift.propDeps_wf s0 (toCmdId x) cc0 D0 hlen0 g2 g3
  have hcl : (toCmdId x).cl ≠ -1 := by
    intro h; have := Hcok.2.1; rw [h] at this; exact absurd this (by decide)
  have hwire : sp.wireOk me bw2 := ⟨Hids.2.1, Hbw2.2⟩
  -- change log C22 (M3): the ack's `Seqnum` is the replica's number of `x` (`propMsgR`'s
  -- `numIs` at `pm.seqnum`; the descriptor's `seqnum` field must carry it from the first
  -- proposal message: descriptor side)
  ihave #Hnq : sp.numAck c.γ c.r b (toCmdId x) sqv $$ []
  · -- round 25: `pdOk`'s `numIs` at the `seqnum` field (`sq'`); the leader's ack carries it.
    -- D23 (SWB-F5): a follower numbered `x` with -1, and its ack's `Seqnum` is unconstrained.
    have hld : ld0 = true ↔ sp.leaderOf c.N b = c.r := g7
    iunfold sp.numAck
    by_cases hme : me = BitVec.srem bw2 (W32 (sint.Z (W64 (c.N : Int))))
    · have hl : sp.leaderOf c.N b = c.r := by
        have h1 := swift.rid_leader bw2 c.N b hN Hbw2.1 Hbw2.2
        rw [← hme] at h1; rw [← h1]; exact Hids.1
      rw [Hsqv hme]
      have hl0 : ld0 = true := hld.2 hl
      subst hl0
      iexists sq'
      isplitl
      · iExactEq Hq0; simp
      · ipureintro; left; rfl
    · have hnl : sp.leaderOf c.N b ≠ c.r := by
        intro h
        exact swift.rid_ne_leader me bw2 c.N b hN Hbw2.1 Hbw2.2 Hids.2.1 hme (by rw [Hids.1, h])
      have hl0 : ld0 = false := by
        cases h : ld0
        · rfl
        · exact absurd (hld.1 h) hnl
      subst hl0
      iexists (W64 (-1))
      isplitl
      · iExactEq Hq0; simp
      · ipureintro; right; rfl
  -- round 53 (52-1): the sender's sequence with `x` and its dependencies (`locDeps`)
  ihave #Hld : sp.locDeps c.γ c.r b (toCmdId x) D0 $$ []
  · iunfold sp.locDeps; iexists s0; iframe Hlb0; ipureintro; exact ⟨hy, List.Perm.of_eq hD⟩
  ihave ⟨#Hfok, %Hhw⟩ := swift.propose_fastAckOk c.γ me bw2 x D0 P0 H0 sqv c.r b Hids.1 Hbw2.1
    hwire g4 hcl $$ [Hpre Hpath Hsh0 Hnq Hld]
  · iframe Hpre Hpath Hsh0 Hnq Hld
  have hsh : swift.handler.shashOf H0.H'.arr = H0 := by cases H0; rfl
  ihave #Hrepr : swift.fastAckRepr (swift.MFastAck.mk me bw2 x pd' hs' sqv)
      ⟨me, bw2, toCmdId x, D0, [H0.H'.arr], sqv⟩ $$ []
  · iunfold swift.fastAckRepr
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    isplitr
    · iexact Hd0
    simp only [List.map_cons, List.map_nil, hsh]
    iexact Hh0
  have hfP : (⟨me, bw2, toCmdId x, D0, [H0.H'.arr], sqv⟩ : sp.FastAck).rep = me ∧
      sp.FastAck.wf ⟨me, bw2, toCmdId x, D0, [H0.H'.arr], sqv⟩ ∧
      D0 ≠ [toCmdId x] ∧ [H0.H'.arr].length + 1 < 2 ^ 62 :=
    ⟨rfl, ⟨hDw, Hhw⟩, hDne, by simp⟩
  ihave Hown := Hbalb $$ Hbal2
  ihave #Hack2 := Hack
  iunfold swift.ackCtx at Hack2
  icases Hack2 with ⟨%sqQ, %szS', %memS', %bt, %sn, %γs, %csv, #HSQ, #HqS, %-, #Hbt, #HbH, #Hsnd,
    #Hsnb, #Hcs, %Hcodes, -⟩
  ihave #Hsctx : swift.sendCtxN c.γ c.γc c.γm c.rp c.N me $$ []
  · iunfold swift.sendCtxN; iexists c.rr, sn, c.γw, γs, csv; iframe Hrr Hrep Hsnd Hsnb Hcs
    ipureintro; exact Hcodes
  ihave HmkOp : iprop(∀ cl : Bool, (if cl then swift.facClientOk c.γ c.γc c.γm
      ⟨me, bw2, toCmdId x, D0, [H0.H'.arr], sqv⟩ else True) -∗
      la2 ↦ swift.MFastAck.mk me bw2 x pd' hs' sqv -∗ swift.fastOpP c.γ c.γc c.γm c.rp la2 cl) $$ []
  · iintro %cl Hcli Hla2
    iunfold swift.fastOpP
    iexists c.N, me, swift.MFastAck.mk me bw2 x pd' hs' sqv, ⟨me, bw2, toCmdId x, D0, [H0.H'.arr], sqv⟩
    iframe Hsctx Hla2 Hrepr Hfok Hcli
    ipureintro; exact hfP
  ihave Hocr : swift.ocfRes d cf cond [] true $$ [Hapf Hocf HPc Hsb Hbs Hbsc]
  · iunfold swift.ocfRes; iframe Hapf Hocf HPc
    iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact ⟨Hb.1, by simp⟩
  wp_bind (If (Val _) _ _)
  iapply (wp_wand (Φ := fun v => iprop(
      ((⌜v = executeVal⌝ ∗ swift.descOwn c RC MP γd d x b
          iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do)) ∗
          swift.ocfRes d cf cond [] true) ∨
        (⌜v = returnVal #()⌝ ∗ swift.descDone c b x d)) ∗
      r_ptr ↦ c.rp ∗ desc_ptr ↦ d ∗ cmdId_ptr ↦ x ∗ msg_ptr ↦ gp)))
    $$ [Hown r desc cmdId msg Hocr Hla2 fastAckSend isRead HmkOp]
  · cases oe
    · wp_auto
      wp_apply (wp_SFA c.γ c.γc c.γm c.rp bt la2) $$ [Hla2 HmkOp]
      · iframe HbH
        iapply HmkOp $$ [] Hla2
        simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      iframe r desc cmdId msg
      ileft; iframe Hown Hocr; ipureintro; rfl
    · ihave ⟨%qe3, %bw3, Hbal3, %Hbw3, Hbalb3⟩ := swift.descOwn_ballot c RC MP γd d x b _ $$ Hown
      wp_auto
      wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw3 _ c.N hN) $$ [$Hbal3 $Hrr $HN]
        as Hbal3
      ihave Hown := Hbalb3 $$ Hbal3
      iunfold swift.ocfRes at Hocr
      icases Hocr with ⟨Hapf, Hocf, HPc, Hsbs⟩
      iunfold swift.proposeHalf at HPc
      icases HPc with ⟨%p, Hp, %Hpv⟩
      have hpn : p ≠ null := by simpa using Hpv
      ihave ⟨Hown, Hp, %gv, #Hgv⟩ := swift.descOwn_propose c RC MP γd d x b
        iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do)) p hpn $$ [Hown Hp]
      · iframe Hown Hp
      ihave #Hgv2 := Hgv
      iStructNamedPrefix Hgv2 "V"
      generalize hR : (frR && !cc.isPut) = R
      generalize hL : decide (me = BitVec.srem bw3 (W32 (sint.Z (W64 (c.N : Int))))) = L
      wp_bind (If (If (Val _) _ _) (Val _) _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #((L && !R) || (R && gv.Proxy'))⌝ ∗
          isRead_ptr ↦ R ∗ desc_ptr ↦ d ∗
          typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Qp).half))))
        $$ [isRead desc Hp]
      · cases L <;> cases R <;> cases hpx : gv.Proxy' <;> wp_auto <;> iframe <;> ipureintro <;>
          simp [hpx]
      iintro %v ⟨%Hv, isRead, desc, Hp⟩
      subst Hv
      by_cases hB : Bool.or (L && !R) (R && gv.Proxy') = true
      · rw [hB]
        wp_auto
        wp_apply (wp_SFA c.γ c.γc c.γm c.rp bt la2) $$ [Hla2 HmkOp]
        · iframe HbH
          iapply HmkOp $$ [] Hla2
          simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        try wp_auto
        -- `r.deliver(desc, cmdId)` (phase `PRE_ACCEPT`, or later: the owner's commit fact;
        -- round 33: `execWhy` and the slot capability from `descSt`, the whole owner state lent)
        ihave Hocr : swift.ocfRes d cf cond [] true $$ [Hapf Hocf Hp Hsbs]
        · iunfold swift.ocfRes; iframe Hapf Hocf Hsbs
          iunfold swift.proposeHalf; iexists p; iframe Hp; ipureintro; simp [hpn]
        ihave ⟨%q, %bw, %stp, %rcp, %dv', %Rs, %Rk, Hrd, HrdR, Hpin, #HRC, #HsB, Hd, HRs, HRk, Hcf, #Hwhy,
          #Hrep, Htix, Hsl, Hback, Hgone⟩ := swift.descOwn_deliver c RC MP γd d x b
            iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do)) cf cond [] true
            $$ [Hown Hocr]
        · iframe Hown Hocr
        ihave #HRCh : swift.RCh c.γ c.γc c.γm c.rp rcp bw $$ []
        · rw [← hRCe]; iexact HRC
        wp_apply (wp_deliver c c.γ c.γc c.γm c.γl c.γw c.γv c.γe c.γo c.γx c.γxe c.γxm c.γxp c.γxu c.γrp c.γcg c.γout c.γcl
            c.γdc γd c.rp c.rr d c.N c.r c.k q q b bw stp rcp dv' x Rs
            iprop(⌜c.sq = true⌝ ∗ c.ret d x ∗ c.env d q)) $$ [Hrd HrdR Hpin Hd HRs Hcf Htix Hsl] as %fin Hfin
        · iframe Hrd HrdR Hpin HRCh HsB Hd HRs Hcf Hwhy Hrep Htix Hsl
          iunfold swift.DC.ctx at Hctx; iexact Hctx
        icases Hfin with ⟨Hrd, HrdR, Hpin, Hfin⟩
        cases fin
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hfin with ⟨Hd, HRs, Htix⟩
          wp_auto
          iframe r desc cmdId msg
          ileft
          isplitr
          · ipureintro; rfl
          iapply Hback $$ Hrd HrdR Hpin Hd HRs Htix HRk
        · simp only [↓reduceIte]
          icases Hfin with ⟨#Hex, HRet⟩
          wp_auto
          iframe r desc cmdId msg
          iright
          isplitr
          · ipureintro; rfl
          iunfold swift.descDone
          iapply Hgone $$ Hrd HrdR Hpin HRk Hex HRet
      · rw [Bool.not_eq_true] at hB
        rw [hB]
        wp_auto
        wp_apply (wp_SFAC c.γ c.γc c.γm c.rp bt la2 _)
          $$ [Hla2 HmkOp]
        · iframe HbH
          iapply HmkOp $$ [] Hla2
          simp only [↓reduceIte]
          iunfold swift.facClientOk
          iexists cc, c.N, frR, lgR
          iframe Hcis HcfgR
          ipureintro
          intro hld
          have hme : me = BitVec.srem bw3 (W32 (sint.Z (W64 (c.N : Int)))) := by
            rcases Classical.em (me = BitVec.srem bw3 (W32 (sint.Z (W64 (c.N : Int))))) with h | hne
            · exact h
            · exact absurd (by rw [← Hbw2.1]; exact hld)
                (swift.rid_ne_leader me bw3 c.N b hN Hbw3.1 Hbw3.2 Hids.2.1 hne)
          rw [← hL, decide_eq_true hme] at hB
          have hR' : R = true := by cases R <;> simp_all
          rw [← hR] at hR'
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hR'
          refine ⟨hR'.1, ?_⟩
          rcases Hcok.1 with h | h
          · rw [h] at hR'; cases hR'.2
          · exact h
        iframe r desc cmdId msg
        ileft; iframe Hown
        isplitr
        · ipureintro; rfl
        iunfold swift.ocfRes; iframe Hapf Hocf Hsbs
        iunfold swift.proposeHalf; iexists p; iframe Hp; ipureintro; simp [hpn]
  iintro %v ⟨Hres, r, desc, cmdId, msg⟩
  icases Hres with (⟨%Hv, Hown, Hocr⟩ | ⟨%Hv, Hdone⟩)
  rotate_left
  · subst Hv
    wp_auto
    iapply HΦ; iright; iexact Hdone
  subst Hv
  wp_auto
  -- `r.handleFastAck(fastAck, desc)` with the own ack (its witness at the leader)
  ihave Hownf : swift.descOwnF c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do)
      $$ [Hown Hocr]
  · iunfold swift.descOwnF
    iframe Hown
    iunfold swift.descOcf
    iexists cf, cond, [], true
    iframe Hocr Hcond
    isplitr
    · iapply swift.ocfV_nil
    iapply BigSepL.bigSepL_nil.2; itrivial
  wp_apply (wp_hfa c γd d x b iprop(swift.descRest c b x d ∗ Do) la
      (swift.MFastAck.mk me bw2 x pd' hs' sqv)) $$ [Hownf] as Hres
  · iframe Hctx Hack Hownf Hla
    isplitr
    · iexists _; iexact Hd0
    isplitr
    · ipureintro; exact ⟨rfl, Hids.2.1⟩
    iright
    iunfold swift.leadWitB
    iright
    iunfold swift.leadWit
    iexists ⟨me, bw2, toCmdId x, D0, [H0.H'.arr], sqv⟩
    iframe Hla Hfok
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    isplitr
    · iexact Hd0
    iexists [H0]; iexact Hh0
  try wp_auto
  icases Hres with (Hownf | Hdone)
  · iapply HΦ; ileft; iexact Hownf
  · iapply HΦ; iright; iexact Hdone


end proof

end Perennial.github_com.imdea_software.swiftpaxos
