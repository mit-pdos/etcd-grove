/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleSyncProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.handleSync(msg)`'s proof (spec: Proof/swift/SyncSpecs.lean, `handleSync.specI`; rounds 11-14,
sv-swa). In Go's order, the whole body (notes/prove-swift.md §18); no sorry. Hypotheses still open (to be discharged by their
owners, notes §18 round 14): `NewReplyChan.specIH` (GAP H-size: sv-swc's restated
`NewReplyChan.specI`, without `historySize`), `stopDescs`'s post (round 14's `propsBack` is gone
with D16: proposals are read-only), `getCmdDesc.syncSpecI`, `EpS_start` (sv-swc's pool),
`cmdIs_wf` (GAP C-wf: discharged in SyncLink by `sp.cmdIs_wf`), no trusted
gap for the last log line (fork c1ecf8e logs `int64(duration)`). The freeing of `cmdDescs` uses `IterCbVN` (Proof/cmap/IterCbN.lean)
over `descsStopped` (GAP S-free closed).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AnyFlag
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncAux
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncTail
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSeq
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
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [sync.atomic.Assumptions] [state.Assumptions] [log.Assumptions]

set_option maxHeartbeats 2000000 in
theorem swift.Replica.handleSync.wp_proofR (EpR EpH : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF) (γ : sp.Names) (γc γm γl γw γv γd γe γo : GName) (n : swift.SyncN) (rp rr : Loc)
    (PC : IProp netDistGF)
    (wp_Now : time.Now.spec (GF := netDistGF) (hG := hG))
    (wp_sorted : swift.sortedProposes.specI (hG := hG))
    (wp_IterCbVN : github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVN.spec (GF := netDistGF))
    (wp_Free : replica.mset.MsgSet.Free.specQ (hG := hG))
    (wp_freeDesc : ∀ b, swift.Replica.freeDesc.specI (hG := hG) (DF b))
    (wp_InitState : state.InitState.spec (GF := netDistGF))
    (wp_IterCbV : github_com.orcaman.concurrent_map.ConcurrentMap.IterCbV.spec (GF := netDistGF))
    (wp_RemoveV : github_com.orcaman.concurrent_map.ConcurrentMap.RemoveV.spec (GF := netDistGF))
    (wp_Store : sync.atomic.Bool.Store.spec (GF := netDistGF) (hG := hG))
    (wp_CNew : github_com.orcaman.concurrent_map.NewV.spec (GF := netDistGF))
    (wp_AQ : replica.QuorumSystem.AQ.spec (hG := hG))
    -- GAP H-size: sv-swc's restated `NewReplyChan.specI` (not landed): `historySize` not taken
    (wp_NRC : swift.NewReplyChan.specIH (hG := hG))
    (wp_syncOrder : swift.syncOrder.specI (hG := hG))
    (wp_keysOf : swift.keysOf.specI (hG := hG))
    (wp_newLKI : swift.lki.newLightKeyInfo.spec (hG := hG))
    (wp_lkiAdd : swift.lki.lightKeyInfo.add.spec (hG := hG))
    (EpS_start : ∀ (N r b' : Nat) (M : sp.SyncMsg), 0 < b' →
      swift.syncCtx γ N r n rp ∗ □ PC ∗ swift.epFresh γ γc γm n γe γd rp rr b' ⊢ |={⊤}=> EpS M [])
    (wp_stop : swift.replyChan.stop.specI (hG := hG) EpR EpH rp)
    (wp_stopD : swift.Replica.stopDescs.specI (hG := hG) EpH γ n γe γd DF PS rr rp)
    (wp_getCD : swift.Replica.getCmdDesc.syncSpecI (hG := hG) EpS γ n.γcl n.γdl rp n.N)
    (wp_Leader : replica.Leader.spec (hG := hG))
    (wp_sendc : replica.Sender.SendToClient.spec (hG := hG))
    (hms : ∀ (l : Loc) (sa : swift.MLightSlowAck) (s : sp.SlowAck), swift.slowAckRepr sa s →
      ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l)
        (.lightSlowAck s) iprop(l ↦ sa))
    (wp_Sub : time.Time.Sub.spec (GF := netDistGF) (hG := hG))
    -- GAP C-wf (§18 round 14): registered commands are well formed (`Cmd.wf`, as `propIs`
    -- requires); an invariant fact not yet in `sp.inv`
    (cmdIs_wf : ∀ (γ : sp.Names) (γc γm γl : GName) (x : sp.CmdId) (c : sp.Cmd),
      sp.inv γ γc γm γl ∗ sp.cmdIs γ x c ⊢ |={⊤}=> ⌜c.wf⌝) :
    swift.Replica.handleSync.specIR (hG := hG) EpR EpS DF PS γ γc γm γl γw γv γd γe γo n rp rr PC := by
  intro ls N r k ld v M0 bs hd w b' M
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, #Hninv, #Hrr, #Hsctx, #HPC, HrdR, Hst, Hep, Hsf, #Hssc, #HMapsP, #HM, #HlbL, Hrow,
    %Hpre⟩
  ihave HMaps := HMapsP
  iunfold swift.syncMaps at HMaps
  icases HMaps with ⟨%rep, %bl, %ph, %cm, %dp, %phM, %cmM, %dpM, #Hls, #Hph, #Hcm, #Hdp, %HMf, #HMs⟩
  iunfold swift.runStS at Hst
  icases Hst with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe, Hpes,
    Hls0, Hlso, Hw, #Hlb, %Hok⟩
  ihave #Hls2 := Hls
  iStructNamedPrefix Hls2 "MS"
  wp_auto
  have hL := Hok.1
  obtain ⟨hvb0, hvc0, hw1, hw2, hst, hnc, -⟩ := hL
  have hbl := HMf.1
  -- the early `return`s: joined (`hcont` when going on)
  try ipersist r
  try ipersist msg
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun vv => iprop(
      (⌜vv = executeVal⌝ ∗ ⌜w.1 ≤ b' ∧ (w.1 = b' → w.2.2.1 = false)⌝ ∗ swift.runStS γ γv rp N r ld v M0 bs hd w b' ∗ 
        (if w.2.2.1 then EpR v.propsM else swift.epStopped n γe γd DF PS rp rr) ∗
        swift.syncFieldsOwn rp) ∨
      (⌜vv = returnVal #()⌝ ∗ ⌜b' < w.1 ∨ (b' = w.1 ∧ w.2.2.1 = true)⌝ ∗ swift.runStS γ γv rp N r ld v M0 bs hd w b' ∗ 
        (if w.2.2.1 then EpR v.propsM else swift.epStopped n γe γd DF PS rp rr) ∗
        swift.syncFieldsOwn rp))))
    $$ [Hbal Hcb Hstat Hhd Hhdl Hhdc Hpr Hprs Hk Hks Hhl Hhls Hpe Hpes Hls0 Hlso Hw Hep Hsf]
  · wp_if_destruct
    · -- `msg.Ballot < r.ballot`: nothing changes
      iright
      isplitr
      · ipureintro; first | rfl | trivial
      isplitr
      · ipureintro; left
        rw [← hbl, hw1]; unfold sp.bal
        have h1 : bl.toInt < v.ballot.toInt := Hif
        have h2 : 0 < bl.toInt.toNat := by rw [← sp.bal, hbl]; exact Hpre.2.2.1
        omega
      iframe Hep Hsf
      iunfold swift.runStS
      iframe
      iframe Hlb
      ipureintro; exact Hok
    wp_if_destruct
    · -- equal ballots
      wp_if_destruct
      · -- in normal operation: nothing changes
        iright
        isplitr
        · ipureintro; first | rfl | trivial
        isplitr
        · ipureintro; right
          exact ⟨by rw [← hbl, hw1], hst.2 (by rw [Hif]; rfl)⟩
        iframe Hep Hsf
        iunfold swift.runStS
        iframe
        iframe Hlb
        ipureintro; exact Hok
      · -- equal ballots, in recovery
        ileft
        isplitr
        · ipureintro; first | rfl | trivial
        isplitr
        · ipureintro
          refine ⟨by rw [hw1, hbl]; exact Nat.le_refl _, fun _ => ?_⟩
          cases h : w.2.2.1
          · rfl
          · exact absurd (by rw [hst.1 h]; rfl) Hif
        iframe Hep Hsf
        iunfold swift.runStS
        iframe
        iframe Hlb
        ipureintro; exact Hok
    · -- a later ballot
      ileft
      isplitr
      · ipureintro; first | rfl | trivial
      isplitr
      · ipureintro
        rename_i Hlt
        have h1 : ¬ bl.toInt < v.ballot.toInt := Hlt
        have h2 : v.ballot.toInt ≠ bl.toInt := fun h => Hif (BitVec.eq_of_toInt_eq h)
        have h3 : 0 ≤ v.ballot.toInt := hvb0
        have h4 : 0 < bl.toInt.toNat := by rw [← sp.bal, hbl]; exact Hpre.2.2.1
        rw [hw1, ← hbl]; unfold sp.bal
        exact ⟨by omega, fun h => absurd (by omega : v.ballot.toInt = bl.toInt) h2⟩
      iframe Hep Hsf
      iunfold swift.runStS
      iframe
      iframe Hlb
      ipureintro; exact Hok
  iintro %vv Hres
  icases Hres with (⟨%Hvv, %hcont, Hst, Hep, Hsf⟩ | ⟨%Hvv, %Hret, Hst, Hep, Hsf⟩)
  rotate_left
  · subst Hvv
    wp_auto
    iapply HΦ
    iframe HrdR
    ileft
    iframe
    ipureintro; exact Hret
  subst Hvv
  wp_auto
  iunfold swift.runStS at Hst
  icases Hst with ⟨Hbal, Hcb, Hstat, Hhd, Hhdl, Hhdc, Hpr, Hprs, Hk, Hks, Hhl, Hhls, Hpe, Hpes,
    Hls0, Hlso, Hw, -, -⟩
  -- the stop, in normal operation: either way the epoch is stopped after it
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun vv => iprop(⌜vv = executeVal⌝ ∗ swift.epStopped n γe γd DF PS rp rr ∗
      swift.syncFieldsOwn rp ∗
      typedPointsto (swift.fld rp go!"status") v.status (DFrac.own (1 : Qp).half))))
    $$ [Hep Hsf Hstat]
  · wp_auto
    wp_if_destruct
    · have hn : w.2.2.1 = true := hst.2 (by rw [Hif]; rfl)
      simp only [hn, ↓reduceIte]
      iunfold swift.syncFieldsOwn at Hsf
      icases Hsf with ⟨%t0, %rc, %fq, %pd, %pdM, Hrs, Hpd, HpdM, Hrc, Hfq⟩
      ihave #Htm1 := swift.time_init $$ Hpkg
      wp_apply wp_Now $$ [$Htm1] as %t _
      try wp_auto
      try wp_auto
      wp_apply (wp_stop rc v.propsM) $$ [$Hep $Hrc] as ⟨HepH, Hrc⟩
      try wp_auto
      try wp_auto
      wp_apply (wp_stopD v.propsM) $$ [$HepH] as Hstp
      try wp_auto
      iframe Hstp Hstat
      isplitr
      · ipureintro; rfl
      iunfold swift.syncFieldsOwn
      iexists t, rc, fq, pd, pdM
      iframe
    · have hn : w.2.2.1 = false := by
        cases h : w.2.2.1
        · rfl
        · exact absurd (by rw [hst.1 h]; rfl) Hif
      simp only [hn, Bool.false_eq_true, ↓reduceIte]
      iframe Hep Hsf Hstat
  iintro %vv ⟨%Hvv, Hstp, Hsf, Hstat⟩
  subst Hvv
  wp_auto
  -- the reproposals: `proposes`' entries the `MSync` lacks are taken out, in `sortedProposes`' order
  ihave #Hctx2 := Hctx
  iunfold swift.runCtxD at Hctx2
  icases Hctx2 with ⟨%rr', %me', %fr, %lg, %dm0, #Hrr', #HisR', %Hcf, #Hinv, #Hcfg, -, -, -, -,
    ⟨%dmc, %γn, %dcap, #HcntL⟩, #Hng⟩
  -- round 47 (task 3): the replica's id, for `getCmdDesc.syncSpecI`'s instance (`ridIs`)
  ihave #Hrid : swift.ridIs rp r $$ []
  · iunfold swift.ridIs
    ihave #HisR2 := HisR'
    iunfold replica.isReplica at HisR2
    icases HisR2 with ⟨%lgA, %cfgpA, %tblA, %pcA, %frA, %nidA, %entsA, %γpcA, %pwslA, %alslA, %latslA,
      %pwsA, %cwmA, -, -, -, #HidA, -⟩
    iexists rr', me'
    iframe Hrr' HidA
    ipureintro; exact Hcf.1
  iapply fupd_wp
  imod swift.props_size ⊤ (by simp) γ γc γm γl v.props v.propsM $$ [Hinv Hprs] with ⟨Hprs, %Hpsz⟩
  · iframe Hinv Hprs
  imodintro
  iunfold swift.propsOwn at Hprs
  icases Hprs with ⟨Hpm, Hpms⟩
  wp_apply wp_slice_literal (V := Loc) []
  isplitr
  · ipureintro; rfl
  iintro %rsl0 ⟨Hrsl, Hrcap⟩
  try wp_auto
  wp_apply (wp_sorted v.props v.propsM (DFrac.own 1)) $$ [$Hpm] as %idsl %ids ⟨Hpm, Hids, %Hids⟩
  · ipureintro; exact Hpsz
  try wp_auto
  ihave %Hidl := ownSlice_len _ _ _ $$ Hids
  ihave HL : (∃ (i : w64) (cv : swift.CommandId) (rsl : GoSlice) (gps : List Loc),
      "i" ∷ i_ptr ↦ i ∗ "cmdId" ∷ cmdId_ptr ↦ cv ∗ "Hr" ∷ reproposed_ptr ↦ rsl ∗
      "Hrsl" ∷ rsl ↦* gps ∗ "Hrcap" ∷ ownSliceCap Loc rsl (DFrac.own 1) ∗
      "Hpm" ∷ v.props ↦$ swift.dropMissing phM (ids.take (sint.nat i)) v.propsM ∗
      "Hpms" ∷ ([∗map] x ↦ gp ∈ swift.dropMissing phM (ids.take (sint.nat i)) v.propsM,
        ∃ c, swift.propIs γ gp (toCmdId x) c) ∗
      "Hreps" ∷ ([∗list] gp ∈ gps, sp.proposeP γ gp) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z idsl.len⌝ : IProp netDistGF)
    $$ [i cmdId reproposed Hrsl Hrcap Hpm Hpms]
  · iexists (W64 0), _, _, []
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, swift.dropMissing, List.foldl_nil]
    iframe
    isplitr
    · iempintro
    ipureintro; exact ⟨by decide, by word⟩
  wp_for HL
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z idsl.len := Hif
    have hiD : sint.nat i < ids.length := by rw [Hidl.1]; word
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z idsl.len := ⟨Hi.1, hlt⟩
    rw [ite_eq_left hb]
    wp_apply wp_load_slice_index (t := swift.CommandId.ty) idsl (sint.Z i) ids _ ids[sint.nat i]
      Hi.1 $$ [Hids] as Hids
    · iframe Hids; ipureintro; exact List.getElem?_eq_getElem hiD
    try wp_auto
    generalize hx : ids[sint.nat i] = x
    have hxi : ids[sint.nat i]? = some x := by rw [← hx]; exact List.getElem?_eq_getElem hiD
    have hxnt : x ∉ ids.take (sint.nat i) :=
      github_com.orcaman.concurrent_map.not_mem_take_of_nodup ids (sint.nat i) x Hids.1 hxi
    have htake : ids.take (sint.nat (i + W64 1)) = ids.take (sint.nat i) ++ [x] := by
      have : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [this, List.take_add_one, hxi]; rfl
    obtain ⟨gp, hgp⟩ : ∃ gp, v.propsM !! x = some gp := by
      have := (Hids.2 x).1 (List.mem_of_getElem? hxi)
      exact Option.isSome_iff_exists.mp this
    have hgpi : swift.dropMissing phM (ids.take (sint.nat i)) v.propsM !! x = some gp := by
      rw [swift.dropMissing_lookup _ _ _ _ hxnt]; exact hgp
    wp_apply wp_map_lookup2 $$ [$Hph] as -
    try wp_auto
    wp_if_destruct
    · -- in the `MSync`: kept
      have hnx : (phM !! x).isSome = true := Hif
      wp_for_post
      iframe
      iexists _, _, _, gps
      rw [htake, swift.dropMissing_snoc]
      simp only [hnx, ↓reduceIte]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · -- the `MSync` lacks `x`: re-proposed
      have hnx : phM !! x = none := by
        cases h : phM !! x
        · rfl
        · rw [h] at Hif; simp at Hif
      wp_apply wp_map_lookup1 $$ [$Hpm] as Hpm
      try wp_auto
      rw [hgpi]
      simp only [Option.getD_some]
      wp_apply wp_slice_literal (V := Loc) [gp]
      isplitr
      · ipureintro; rfl
      iintro %s1 ⟨Hs1, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hrsl Hrcap Hs1] as %nsl ⟨Hrsl, Hrcap, -⟩
      · iframe
      try wp_auto
      wp_apply wp_mapDelete $$ [$Hpm] as Hpm
      try wp_auto
      icases (BigSepM.bigSepM_delete hgpi).1 $$ Hpms with ⟨⟨%cx, #Hgp⟩, Hpms⟩
      ihave Hpp := swift.propIs_proposeP γ gp (toCmdId x) cx $$ Hgp
      wp_for_post
      iframe
      iexists _, _, _, (gps ++ [gp])
      rw [htake, swift.dropMissing_snoc]
      simp only [hnx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      ihave Hreps := (BigSepL.bigSepL_snoc (Φ := fun _ g => sp.proposeP γ g) (l := gps)
        (x := gp)).2 $$ [Hreps]
      · iframe Hreps; iexact Hpp
      iframe
      ipureintro; exact ⟨by word, by word⟩
  -- after the loop: `proposes` keeps the `MSync`'s entries
  have hiv : sint.nat i = ids.length := by
    have : ¬ sint.Z i < sint.Z idsl.len := Hif
    rw [Hidl.1]; word
  rw [hiv, List.take_length] at *
  have hpM : ∀ x, swift.dropMissing phM ids v.propsM !! x =
      if (phM !! x).isSome then v.propsM !! x else none :=
    swift.dropMissing_all phM ids v.propsM (fun k hk => (Hids.2 k).2 hk)
  generalize swift.dropMissing phM ids v.propsM = pM1 at *
  try wp_auto
  -- the stopped descriptors freed, each once (GAP S-free: `descsStopped`, `IterCbVN`)
  iunfold swift.epStopped at Hstp
  icases Hstp with ⟨%bw, %st, %stp, %stpX, %bc, Hb2, Hst2, HState, Hrc2, Htok, Hxp, Hxe, Hrm, Hds,
    Hout, ⟨%hs, Hhs⟩, Hfz, ⟨%fq, Hfq1, Hfq2⟩⟩
  iunfold swift.descsStopped at Hds
  icases Hds with ⟨%dm1, %γdc, %Mc, Hcd, #Hdm1, Hrd1, Hview, #HpoolS, HPS, Hents⟩
  -- round B1 (D82 (4)): the stopped view's facts spent for the free law (the descriptor side:
  -- the stopped epoch's free permit, `swift.freeSp`)
  iapply fupd_wp
  imod swift.descPoolCtxS_F (DF bc.2) (PS bc.2) rp Mc $$ [HpoolS HPS] with #Hpool
  · iframe HpoolS HPS
  imodintro
  wp_method_call
  try wp_auto
  wp_apply (github_com.orcaman.concurrent_map.ConcurrentMap.wp_IterCbOwnN wp_IterCbVN dm1 γdc
      (swift.descR γd) _ Mc (fun vis => iprop([∗map] _k ↦ vv ∈
        (vis.map Prod.fst).foldl (fun M k => GMap.delete k M) Mc, ∃ d : Loc,
          ⌜vv = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
          swift.descFree (DF bc.2) d)))
    $$ [Hrd1 Hview Hents] as ⟨Hrd1, Hview, %vis, -, %Hvis⟩
  · iframe Hrd1 Hview
    isplitl [Hents]
    · simp only [List.map_nil, List.foldl_nil]; iexact Hents
    imodintro
    iintro %vis %k %vv %Φ' %Hkf - HJ HΦ'
    obtain ⟨hk, hfresh⟩ := Hkf
    have hk' : (vis.map Prod.fst).foldl (fun M k => GMap.delete k M) Mc !! k = some vv := by
      rw [swift.foldl_delete_lookup _ _ _ hfresh]; exact hk
    icases (BigSepM.bigSepM_delete hk').1 $$ HJ with ⟨⟨%d, %Hvd, Hd⟩, HJ⟩
    subst Hvd
    iunfold swift.descFree at Hd
    icases Hd with ⟨%m0, %s0, %sl, %fa, Hmsgs, Hstop, Hslow, Hfast, Hfs, Hff, HDF⟩
    wp_auto
    iunfold swift.msgSetFree at Hfs Hff
    icases Hfs with ⟨%q1, %sz1, %mem1, %P1, %A1, %PL1, %R1, %hd1, Hfs, HR1⟩
    icases Hff with ⟨%q2, %sz2, %mem2, %P2, %A2, %PL2, %R2, %hd2, Hff, HR2⟩
    wp_apply (wp_Free sl q1 sz1 mem1 P1 A1 PL1 R1 hd1) $$ [Hfs HR1] as ⟨-, Hfs⟩
    · iframe
    try wp_auto
    wp_apply (wp_Free fa q2 sz2 mem2 P2 A2 PL2 R2 hd2) $$ [Hff HR2] as ⟨-, Hff⟩
    · iframe
    try wp_auto
    wp_apply (wp_freeDesc bc.2 rp d) $$ [Hmsgs Hstop Hslow Hfast HDF Hfs Hff]
    · iframe Hpool
      iunfold swift.descPooled
      iexists _, _, _, _
      iframe
      iunfold swift.msetAny
      isplitl [Hfs]
      · icases Hfs with (%Hn | Hfs)
        · ileft; ipureintro; exact Hn
        · iright; iapply replica.mset.ownD_ownAny $$ Hfs
      · icases Hff with (%Hn | Hff)
        · ileft; ipureintro; exact Hn
        · iright; iapply replica.mset.ownD_ownAny $$ Hff
    try wp_auto
    iapply HΦ'
    have hfold : ((vis ++ [(k, interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)]).map
        Prod.fst).foldl (fun M k => GMap.delete k M) Mc =
        GMap.delete k ((vis.map Prod.fst).foldl (fun M k => GMap.delete k M) Mc) := by
      simp [List.foldl_append]
    rw [hfold]
    iexact HJ
  try wp_auto
  -- `State = InitState()`
  ihave %Hrreq := typedPointsto_agree_wand _ _ _ _ _ $$ Hrr Hrr'
  subst Hrreq
  wp_apply wp_InitState as %stp' Hstp'
  try wp_auto
  -- the delivered phase: removal mode, `delivered` emptied
  ihave #Hsctx2 := Hsctx
  iunfold swift.syncCtx at Hsctx2
  icases Hsctx2 with ⟨%dmd, #Hdmd, #Hdmv, #HdI, #HexL, #HacL, #HbaL, #Hany, #Hhook, #Hfm,
    ⟨%qs, #Hqs, #HQS⟩, ⟨%hsl, %rr2, #Hhsl, %Hhsl, #Hrr2, #Hshut⟩, ⟨%dmc2, %dcap2, #HcntL2⟩, %HnN, -, -⟩
  iapply fupd_wp
  imod swift.epoch_view_agree γ γv γe γo k w bc $$ [Hninv Hw Htok] with ⟨Hw, Htok, %Hagree⟩
  · iframe Hninv Hw Htok
  iunfold swift.runReader at HrdR
  icases HrdR with ⟨%dmr, #Hdmr, Hrdd⟩
  ihave %Hdmeq := typedPointsto_agree_wand _ _ _ _ _ $$ Hdmd Hdmr
  subst Hdmeq
  imod swift.deliv_rm_start ⊤ (by simp) γ N r n.γdl n.γx n.γxp n.γxm n.γa n.γxe n.γrm n.str bc.2
    stpX $$ [HdI Hxp Hxe Hrm] with ⟨%Md, Hrm⟩
  · iframe HdI Hxp Hxe Hrm
  imodintro
  wp_apply wp_slice_literal (V := GoString) []
  isplitr
  · ipureintro; rfl
  iintro %dsl0 ⟨Hdsl, Hdcap⟩
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply (swift.deliv_iter wp_IterCbV γ N r n.γdl n.γx n.γxp n.γxm n.γa n.γxe n.γrm n.str dmd _ Md
      (bc.2, stpX) false (fun vis => iprop(∃ sl : GoSlice, dkeys_ptr ↦ sl ∗
        sl ↦* (vis.map Prod.fst) ∗ ownSliceCap GoString sl (DFrac.own 1))))
    $$ [Hrdd Hrm dkeys Hdsl Hdcap] as ⟨Hrdd, Hrm, %vis, ⟨%dsl, Hdk, Hdsl, Hdcap⟩, %Hvis⟩
  · iframe HdI Hrdd Hrm
    isplitl [dkeys Hdsl Hdcap]
    · iexists _; simp only [List.map_nil]; iframe
    imodintro
    iintro %vis %k %wv %Φ' %hk - ⟨%sl, Hdk, Hsl, Hcap⟩ HΦ'
    wp_auto
    wp_apply wp_slice_literal (V := GoString) [k]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨Hs1, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hs1] as %nsl ⟨Hsl, Hcap, -⟩
    · iframe
    try wp_auto
    iapply HΦ'
    iexists nsl
    iframe
    simp only [List.map_append, List.map_cons, List.map_nil]
    iexact Hsl
  try wp_auto
  ihave %Hdl := ownSlice_len _ _ _ $$ Hdsl
  ihave HL2 : (∃ (i : w64) (kv : GoString),
      "i" ∷ i_ptr ↦ i ∗ "k" ∷ k_ptr ↦ kv ∗
      "Hrm" ∷ swift.rmTok n.γrm (some ((((vis.map Prod.fst).take (sint.nat i)).foldl
        (fun M k => GMap.delete k M) Md), (bc.2, stpX), false)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z dsl.len⌝ : IProp netDistGF) $$ [i k Hrm]
  · iexists (W64 0), _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for HL2
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z dsl.len := by simpa using Hif
    have hiD : sint.nat i < (vis.map Prod.fst).length := by rw [Hdl.1]; word
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dsl.len := ⟨Hi.1, hlt⟩
    rw [ite_eq_left hb]
    wp_apply wp_load_slice_index (t := go.string) dsl (sint.Z i) (vis.map Prod.fst) _
      (vis.map Prod.fst)[sint.nat i] Hi.1 $$ [Hdsl] as Hdsl
    · iframe Hdsl; ipureintro; exact List.getElem?_eq_getElem hiD
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply (swift.deliv_remove wp_RemoveV γ N r n.γdl n.γx n.γxp n.γxm n.γa n.γxe n.γrm n.str dmd
      _ _ (bc.2, stpX) false) $$ [Hrm] as Hrm
    · iframe HdI Hdmv Hrm
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    have htake : (vis.map Prod.fst).take (sint.nat (i + W64 1)) =
        (vis.map Prod.fst).take (sint.nat i) ++ [(vis.map Prod.fst)[sint.nat i]] := by
      have : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [this, List.take_add_one, List.getElem?_eq_getElem hiD]; rfl
    rw [htake, List.foldl_append]
    iframe
    ipureintro; exact ⟨by word, by word⟩
  -- the view is empty
  have hiv : sint.nat i = (vis.map Prod.fst).length := by
    have : ¬ sint.Z i < sint.Z dsl.len := by simpa using Hif
    rw [Hdl.1]; word
  have hempty : ((vis.map Prod.fst).take (sint.nat i)).foldl (fun M k => GMap.delete k M) Md =
      ∅ := by
    rw [hiv, List.take_length]; exact swift.keys_delete_empty vis Md Hvis
  rw [hempty]
  try wp_auto
  wp_apply (swift.wp_anyStore wp_Store rp false) $$ Hany
  try wp_auto
  -- under `execL`: `execLog = nil`, the record reset to the new epoch `b'`
  have hcb : w.2.1 < b' := by
    cases hn : w.2.2.1
    · have := Hpre.2.2.2 hn; omega
    · have h1 : w.1 ≠ b' := fun h => by have := hcont.2 h; rw [hn] at this; cases this
      omega
  have hbc2 : bc.2 < b' := by rw [Hagree]; exact hcb
  wp_apply sync.Mutex.wp_Lock $$ [$HexL] as ⟨Hxlk, HX⟩
  iunfold swift.execLInvE at HX
  icases HX with ⟨%xsl, %xes, %bX, %X, %stpX2, Hxlog, -, -, Hgx, Hgxe, -, -, -, -, -⟩
  try wp_auto
  have happ : swift.applyX [] = fun _ => none := rfl
  rw [← happ]
  iapply fupd_wp
  imod swift.execL_reset γ N r n.γdl n.γx n.γxp n.γxm n.γa n.γxe n.γrm n.γxu n.str rp bc.2 stpX b' stp'
    hbc2 bX X stpX2 $$ [HdI Hrm Hgx Hgxe Hxlog Hstp'] with ⟨HX, Hrm, %HbX⟩
  · iframe HdI Hrm Hgx Hgxe Hxlog
    iexact Hstp'
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$HexL $Hxlk $HX]
  try wp_auto
  -- `routineCount = 0` under `cntL`
  wp_apply sync.Mutex.wp_Lock $$ [$HcntL2] as ⟨Hclk, HC⟩
  iunfold swift.cntLInvR at HC
  icases HC with ⟨%sq, %rc0, %T0, Hsq, Hrc0, HcG⟩
  try wp_auto
  -- round 17 (SWB-14's fix): `stopDescs` froze `cntL`'s registry at count 0 (`epStopped`'s
  -- `cntFrozen … true`); the reset writes 0 over 0 and clears the flag for the new epoch
  imod swift.cntLGhost_unfreeze n.γn dmc2 n.γdl dcap2 rc0 T0 $$ [$HcG $Hfz] with ⟨%HcT, HcG0, Hfz⟩
  obtain ⟨hrc0, hT0⟩ := HcT
  subst hrc0 hT0
  wp_apply sync.Mutex.wp_Unlock $$ [$HcntL2 $Hclk Hsq Hrc0 HcG0]
  · iunfold swift.cntLInvR; iexists _, _, []; iframe
  try wp_auto
  -- the new `cmdDescs`, `proposeDeps`
  ihave ⟨%nsh, Hsh⟩ := github_com.orcaman.concurrent_map.isCMapV_shards _ _ _ $$ Hdmv
  iunfold github_com.orcaman.concurrent_map.cmapShards at Hsh
  icases Hsh with ⟨%wsh, #Hsh, %Hwsh⟩
  wp_apply (wp_CNew wsh (swift.descR γd)) $$ [$Hsh] as %dm2 ⟨%γdc2, #Hdm2, Hv2, Hrd2⟩
  · ipureintro; obtain ⟨h1, h2⟩ := Hwsh; subst h1; word
  try wp_auto
  iunfold swift.syncFieldsOwn at Hsf
  icases Hsf with ⟨%t0, %rc1, %fq0, %pd, %pdM, Hrs, Hpd, HpdM, Hrc1, Hfq0⟩
  -- round 23 (D18 G2): `FQ` whole again (`syncFieldsOwn`'s quarter, the stopped epoch's rest)
  ihave ⟨-, Hfq2⟩ := typedPointsto_half_combine _ _ _ (1 : Qp).half $$ [Hfq0 Hfq2]
  · iframe
  ihave ⟨-, Hfq⟩ := typedPointsto_half_combine _ _ _ (1 : Qp) $$ [Hfq1 Hfq2]
  · iframe
  try wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := GoSlice)) as %pd' Hpd'
  ihave ⟨%Hsteq, Hstat⟩ := typedPointsto_half_combine _ _ _ (1 : Qp) $$ [Hstat Hst2]
  · iframe
  try wp_auto
  -- `ballot := msg.Ballot` under `ballotL` (its quarter, the run loop's quarter, the epoch's half)
  wp_apply sync.Mutex.wp_Lock $$ [$HbaL] as ⟨Hblk, HB⟩
  iunfold swift.ballotLInv at HB
  icases HB with ⟨%bq, HBq, -⟩
  ihave ⟨%Hbq, Hbal⟩ := typedPointsto_half_combine _ _ _ (1 : Qp).half $$ [HBq Hbal]
  · iframe
  ihave ⟨%Hbq2, Hbal⟩ := typedPointsto_half_combine _ _ _ (1 : Qp) $$ [Hbal Hb2]
  · iframe
  try wp_auto
  icases (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hbal with ⟨Hbal, Hb2⟩
  icases (typedPointsto_half_split _ _ (1 : Qp).half).1 $$ Hbal with ⟨Hbal, HBq⟩
  have hbl0 : 0 ≤ sint.Z bl := by
    have h2 : 0 < bl.toInt.toNat := by rw [← sp.bal, hbl]; exact Hpre.2.2.1
    show 0 ≤ bl.toInt; omega
  wp_apply sync.Mutex.wp_Unlock $$ [$HbaL $Hblk HBq]
  · inext; iunfold swift.ballotLInv; iexists bl; iframe; ipureintro; exact hbl0
  try wp_auto
  -- `FQ := qs.AQ(ballot)` (`fixedMajority`)
  wp_apply (wp_AQ qs N bl) as %aqp #Haq
  · iframe #; ipureintro; exact hbl0
  -- round 23 (D18 G2): the new `FQ` is a fast quorum of `b'` (for `epFresh`)
  have hb'q : (sint.Z bl).toNat = b' := by rw [← hbl]; rfl
  ihave #HFQok : swift.fqOk (interface.mkOk replica.Quorum.ty #aqp) n.N b' $$ [Haq]
  · rw [← hb'q, HnN]; iapply swift.aq_fqOk N _ ⟨Hcf.2.2.2.1, Hcf.2.2.2.2.1⟩ aqp; iexact Haq
  try wp_auto
  icases (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hfq with ⟨Hfq1, Hfq2⟩
  icases (typedPointsto_half_split _ _ (1 : Qp).half).1 $$ Hfq2 with ⟨Hfq2, Hfq3⟩
  -- the new reply channel (its cell unfilled: the new epoch's)
  ihave %Hrreq2 := typedPointsto_agree_wand _ _ _ _ _ $$ Hrr Hrr2
  subst Hrreq2
  iapply fupd_wp
  imod swift.cell_alloc swift.replyCellN ⊤ (swift.replyCellRes rp bl) with ⟨%γrl, #Hcell, Hfill, Hclaim⟩
  imodintro
  wp_apply (wp_NRC rp rr hsl γ γc γm γrl bl) $$ [Hclaim] as %rc2 HrcH
  · iframe; iframe #; ipureintro; exact Hhsl
  icases Hrc2 with ⟨%rc0, Hrc2⟩
  ihave ⟨%Hrceq, Hrc⟩ := typedPointsto_half_combine _ _ _ (1 : Qp) $$ [Hrc1 Hrc2]
  · iframe
  try wp_auto
  icases (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hrc with ⟨Hrc1, Hrc2⟩
  -- GAP H-size (§18, closed on the spec side): `historySize` is the stopped epoch's
  -- (`epStopped`), `NewReplyChan.specIH` does not take it; Go's `r.historySize = 0` here, then
  -- it goes to the new epoch (`epFresh`, the cell's content when the epoch fills it)
  try wp_auto
  -- taking ballot `b'`'s `MSync` in the node state (ghost): the order's `accepted` facts
  obtain ⟨-, -, hrN, -, -, hnode⟩ := Hcf
  -- L2: at its resolution (`ghostTakeSync(msg.Ballot)`, `takeSync_stepD` in its update)
  ihave #Hcpk : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client
    $$ []
  · iPkgInit
  wp_bind (App (Val (@! swift.resolveTakeSync)) (Val _))
  iapply (swift.wp_resolveTakeSync γ k bl
    iprop(ghostVar γv (1 : Qp).half (w.tookSync b' (sp.syncOrder M)) ∗
      swift.epochTok γe (1 : Qp).half (b', b') ∗
      ([∗list] i ↦ x ∈ sp.syncOrder M, sp.locAt γ r b' i x) ∗
      ([∗list] x ∈ sp.syncOrder M, sp.accepted γ r b' x) ∗
      ([∗list] y ∈ sp.syncOrder M, swift.claimTok (n.sn N r).γcl (b', y) .sync) ∗
      ghostMapElem (n.sn N r).γcg (b', false) (DFrac.own 1) (none : Option GName)))
    $$ [Hw Htok Hrow]
  · iframe Hpkg Hcpk Hng
    isplitr
    · ipureintro; exact hbl0
    iunfold swift.resolveUpd
    iintro %W' Hpre
    rw [hbl]
    imod swift.takeSync_stepD (⊤ \ ↑client.nodeProphN) swift.nodeN_pE swift.spN_pE γ γc γm γl γv γe γo N r k fr lg w bc b' M hrN hnode hcont.1 hcb W'
      $$ [Hw Htok Hrow Hpre] with ⟨Hw, Hpost, Htok, #Hlocs, #Haccs, Hrows, Hcgr⟩
    · iframe Hinv Hcfg Hninv Hw Htok HM Hrow Hpre
    imodintro
    iframe Hpost Hw Htok Hrows Hcgr Hlocs Haccs
  inext
  iintro ⟨Hw, Htok, #Hlocs, #Haccs, Hrows, Hcgr⟩
  try wp_auto
  -- under `acceptL`: `accepted` the `MSync`'s commands, `waiting` empty; removal mode ends
  wp_apply sync.Mutex.wp_Lock $$ [$HacL] as ⟨Halk, HA⟩
  iunfold swift.acceptInv at HA
  icases HA with ⟨%am, %wm, %A, %W, %bA, Haf, -, Hwf, -, -, Ha, -, Hrk⟩
  iunfold swift.recheckOwn at Hrk
  icases Hrk with ⟨%rk, %rids, Frk, -, -⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %am' Ham'
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun keys i => iprop(∃ (cv : swift.CommandId) (A1 : GMap swift.CommandId Unit),
      cmdId_ptr ↦ cv ∗ swift.fld rp go!"accepted" ↦ am' ∗ am' ↦$ A1 ∗
      ⌜∀ d, (A1 !! d).isSome → (phM !! d).isSome⌝))) $$ Hph
  iintro %keys %hkeys
  isplitl [cmdId Ham' Haf]
  · iexists _, ∅
    iframe
    ipureintro; intro d h; simp at h
  isplitl []
  · imodintro
    iintro %j %key %u ⟨%hk1, %hk2⟩ ⟨%cv, %A1, Hc, Haf, Ham', %HA1⟩
    wp_auto
    wp_apply wp_mapInsert $$ [$Ham'] as Ham'
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplit
    · ipureintro; rfl
    · iexists _, _
      iframe
      ipureintro
      intro d hd
      by_cases hdk : d = key
      · subst hdk; rw [hk2]; rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdk)] at hd; exact HA1 d hd
  iintro ⟨%cv, %A1, Hc, Haf, Ham', %HA1⟩ -
  try wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := GoSlice)) as %wm' Hwm'
  try wp_auto
  iapply fupd_wp
  imod swift.acceptL_reset γ N r n.γdl n.γx n.γxp n.γxm n.γa n.γxe n.γrm n.str rp b' stp' bA am'
    wm' A1 $$ [HdI Hrm Ha Haf Ham' Hwf Hwm' Frk] with ⟨HAI, Hrm, Hxp', Hxe'⟩
  · iframe
    isplitr
    · iexact HdI
    imodintro
    iintro %d %hd
    have hdM : toCmdId d ∈ sp.syncOrder M :=
      sp.syncOrder_complete M HMf.2.1 _ ((HMf.2.2 d).1 (HA1 d hd))
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdM
    iapply (BigSepL.bigSepL_lookup hj) $$ Haccs
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$HacL $Halk $HAI]
  try wp_auto
  -- the order, the run loop's maps reset
  wp_apply (wp_syncOrder ls b' M) $$ [] as %osl ⟨Hosl, Hocap⟩
  · iframe #; ipureintro; exact Hpre.2.1
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface)) as %km' Hkm'
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %hm' Hhm'
  try wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %pp' Hpp'
  try wp_auto
  -- the keys' rebuild along the `MSync`'s sequence
  iapply fupd_wp
  imod sp.sync_kinds ⊤ (by simp) b' M $$ [Hinv HM] with %Hkinds
  · iframe Hinv HM
  imodintro
  ihave %Hosll := ownSlice_len _ _ _ $$ Hosl
  ihave HO : (∃ (j : w64) (cv : swift.CommandId) (kM : GMap w64 GoInterface),
      "i" ∷ i_ptr ↦ j ∗ "cmdId" ∷ cmdId_ptr ↦ cv ∗ "Hkmm" ∷ km' ↦$ kM ∗
      "HkI" ∷ swift.keysIn kM ((sp.syncSeq M).take (sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len⌝ : IProp netDistGF)
    $$ [i cmdId Hkm']
  · iexists (W64 0), _, ∅
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    isplitl []
    · iapply swift.keysIn_nil
    ipureintro; exact ⟨by decide, by word⟩
  wp_for HO
  wp_if_destruct
  · have hjO : sint.nat j < (sp.syncOrder M).length := by
      have := Hosll.1; simp at this; rw [this]; word
    obtain ⟨y, hy⟩ : ∃ y, (sp.syncOrder M)[sint.nat j]? = some y :=
      ⟨_, List.getElem?_eq_getElem hjO⟩
    rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len from ⟨Hj.1, Hif⟩)]
    wp_apply (wp_load_slice_index (V := swift.CommandId) osl (sint.Z j) _ _ (ofCmdId y) Hj.1)
      $$ [Hosl] as Hosl
    · iframe; ipureintro
      rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hy]; rfl
    try wp_auto
    -- `cmd := msg.Cmds[cmdId]`
    obtain ⟨q, hqM, hqy⟩ : ∃ q ∈ M, q.1 = y := by
      have := sp.syncOrder_mem M y (List.mem_of_getElem? hy)
      obtain ⟨q, hq, h⟩ := List.mem_map.mp this
      exact ⟨q, hq, h⟩
    obtain ⟨iq, hiq⟩ := List.mem_iff_getElem?.mp hqM
    icases (BigSepL.bigSepL_lookup hiq) $$ HMs with ⟨%vs, %dsl, %Hql, #Hvs, #Hdsl⟩
    subst hqy
    wp_apply (wp_map_lookup1 _ _ cm cmM (ofCmdId q.1)) $$ Hcm as -
    rw [Hql.1]
    simp only [Option.getD_some]
    try wp_auto
    have hpg := Hkinds q hqM
    have hop : q.2.1.op ≠ swift.opSCAN := by
      rcases hpg with h | h
      · unfold sp.Cmd.isPut sp.opPUT at h; simp at h; rw [h]; decide
      · unfold sp.Cmd.isGet sp.opGET at h; simp at h; rw [h]; decide
    wp_apply (wp_keysOf q.2.1 vs) $$ [] as %ksl Hksl
    · ipureintro; exact hop
    ihave %Hkl := ownSlice_len _ _ _ $$ Hksl
    try wp_auto
    obtain ⟨pre, hpre⟩ : ∃ s, s = (sp.syncSeq M).take (sint.nat j) := ⟨_, rfl⟩
    rw [← hpre]
    ihave HL : (∃ (i : w64) (kv : w64),
        "ii" ∷ i_ptr ↦ i ∗ "kk" ∷ k_ptr ↦ kv ∗
        "HL" ∷ ((⌜i = W64 0⌝ ∗ km' ↦$ kM ∗ swift.keysIn kM pre) ∨
          (⌜i = W64 1⌝ ∗ ∃ kM' : GMap w64 GoInterface, km' ↦$ kM' ∗
            swift.keysIn kM' (pre ++ [(q.1, q.2.1)]))) : IProp netDistGF)
      $$ [i k Hkmm HkI]
    · iexists (W64 0), _
      iframe
      ileft
      iframe
      ipureintro; rfl
    wp_for HL
    have hlen1 : sint.Z ksl.len = 1 := by
      have := Hkl.1; simp at this; word
    icases HL with (⟨%Hi0, Hkmm, HkI⟩ | ⟨%Hi1, %kM', Hkmm, HkI⟩)
    rotate_left
    · -- after the key
      subst Hi1
      wp_if_destruct
      · exfalso; rw [hlen1] at Hif; exact absurd Hif (by decide)
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, _, kM'
      have hsj : (sp.syncSeq M)[sint.nat j]? = some (q.1, q.2.1) := by
        rw [sp.syncSeq_eq, List.getElem?_map, hy]
        simp [sp.syncCmd_of_mem HMf.2.1 hqM]
      have htk : (sp.syncSeq M).take (sint.nat (j + W64 1)) = pre ++ [(q.1, q.2.1)] := by
        rw [hpre, show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hsj]
        rfl
      rw [htk]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    subst Hi0
    wp_if_destruct
    rotate_left
    · exfalso; rw [hlen1] at Hif; exact Hif (by decide)
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len from
      ⟨by decide, by rw [hlen1]; decide⟩)]
    wp_apply wp_load_slice_index (t := state.Key.ty) ksl (sint.Z (W64 0)) [q.2.1.key] _ q.2.1.key
      (by decide) $$ [Hksl] as Hksl
    · iframe Hksl; ipureintro; rfl
    try wp_auto
    iunfold swift.keysIn at HkI
    icases HkI with ⟨HkE, %Hkcov⟩
    ihave HkI : swift.keysIn kM pre $$ [HkE]
    · iunfold swift.keysIn; iframe HkE; ipureintro; exact Hkcov
    wp_apply wp_map_lookup2 $$ [$Hkmm] as Hkmm
    wp_join iprop(∃ (kl : Loc) (kMn : GMap w64 GoInterface),
        k_ptr ↦ q.2.1.key ∗ swift.fld rp go!"keys" ↦ km' ∗
        info_ptr ↦ (interface.ok ⟨go.GoType.PointerType swift.lightKeyInfo.ty, #kl⟩ : GoInterface) ∗
        km' ↦$ kMn ∗
        swift.lki.lkiOwn kl (swift.lkOf pre q.2.1.key).1 (swift.lkOf pre q.2.1.key).2 ∗
        (swift.lki.lkiOwn kl
            (swift.lki.addTo q.2.1.op (ofCmdId q.1) (swift.lkOf pre q.2.1.key).1
              (swift.lkOf pre q.2.1.key).2).1
            (swift.lki.addTo q.2.1.op (ofCmdId q.1) (swift.lkOf pre q.2.1.key).1
              (swift.lkOf pre q.2.1.key).2).2 -∗
          swift.keysIn kMn (pre ++ [(q.1, q.2.1)])))
      with [kk Hk info Hkmm HkI] as ⟨%kl, %kMn, kk, Hk, info, Hkmm, Hlki, Hkback'⟩
    · -- the key has a `lightKeyInfo`
      obtain ⟨ki, hki⟩ := Option.isSome_iff_exists.mp Hif
      ihave ⟨%kl, %Hkl, Hlki, Hkback'⟩ := swift.keysIn_lookup kM pre q.1 q.2.1 ki hki $$ HkI
      rw [hki, Hkl]
      simp only [Option.getD_some]
      try wp_auto
      try wp_join_done
      iexists kl, kM
      iframe
    · -- a fresh `lightKeyInfo`
      have hnone : kM !! q.2.1.key = none := by simpa using Hif
      have h0 := Hkcov q.2.1.key hnone
      wp_apply wp_newLKI as %kl Hlki
      try wp_auto
      wp_apply wp_mapInsert $$ [$Hkmm] as Hkmm
      try wp_auto
      try wp_join_done
      iexists kl, _
      iframe
      isplitl [Hlki]
      · rw [h0]; iexact Hlki
      iintro Hl
      rw [h0]
      iapply swift.keysIn_new kM pre q.1 q.2.1 kl hnone
      iframe
    try wp_auto
    have hClen : (swift.lkOf pre q.2.1.key).2.length + 1 < 2 ^ 63 := by
      have := swift.lkOf_len pre q.2.1.key
      have h2 : pre.length ≤ M.length := by
        rw [hpre]
        have : (sp.syncSeq M).length = M.length := by
          rw [sp.syncSeq_eq, List.length_map]
          rw [← List.length_map (f := Prod.fst)]
          exact ((List.perm_ext_iff_of_nodup (sp.syncOrder_nodup M) HMf.2.1).mpr
            (fun x => ⟨sp.syncOrder_mem M x, sp.syncOrder_complete M HMf.2.1 x⟩)).length_eq
        rw [← this]; exact List.length_take_le' _ _
      have := Hpre.2.1
      omega
    wp_apply (wp_lkiAdd kl _ _ (state.Command.mk q.2.1.op q.2.1.key vs) (ofCmdId q.1)) $$ [$Hlki] as Hlki
    · ipureintro; exact hClen
    ihave HkI' := Hkback' $$ [Hlki]
    · iExactEq Hlki; rfl
    try wp_auto
    wp_for_post
    iframe
    iexists (W64 0 + W64 1), q.2.1.key
    iframe
    iright
    isplitr
    · ipureintro; decide
    iexists kMn
    iframe
  -- the keys rebuilt: `keysOwn` along `syncSeq M`
  have hseqlen : (sp.syncSeq M).length = sint.nat j := by
    have := Hosll.1; simp at this
    rw [sp.syncSeq_eq, List.length_map, this]
    have : ¬ sint.Z j < sint.Z osl.len := Hif
    word
  rw [← hseqlen, List.take_length]
  ihave Hks' := swift.keysIn_own km' kM (sp.syncSeq M) $$ [Hkmm HkI]
  · iframe
  -- the new epoch (its descriptors to come): `EpS M []` (the pool's allocation, `EpS_start`)
  icases (typedPointsto_half_split _ _ (1 : Qp)).1 $$ Hstat with ⟨Hstat, Hstat2⟩
  iapply fupd_wp
  imod (EpS_start N r b' M Hpre.2.2.1) $$ [Hb2 Hstat2 HState Hrc2 HrcH Hfill Htok Hxp' Hxe'
      Hrm Hcd Hv2 Hrd2 Hhs Hfz Hfq1 Hfq2 Hout Hcgr] with HEp
  · isplitr
    · iexact Hsctx
    isplitr
    · imodintro; iexact HPC
    iunfold swift.fqOk at HFQok
    icases HFQok with ⟨%szF, %memF, #HqF, %HmF⟩
    iunfold swift.epFresh
    iexists bl, stp', rc2, γrl
    iframe
    isplitl [Hcd Hv2 Hrd2]
    · iunfold swift.descsFresh
      iexists dm2, γdc2
      iframe
      iframe #
    isplitr
    · ipureintro; exact hbl
    iexists szF, memF
    iframe
    iframe HqF
    ipureintro; exact HmF
  -- the `MSync`'s commands are registered
  imod sp.syncIs_cmdIs ⊤ (by simp) b' M $$ [Hinv HM] with #Hcmds
  · iframe Hinv HM
  -- round 48 (47-a, D64): the replica's `locLb` of the `MSync`'s sequence, for every entry
  imod sp.syncIs_seq ⊤ (by simp) b' M $$ [Hinv HM] with %Hseq
  · iframe Hinv HM
  ihave #Hlb := sp.locLb_syncSeq r b' M Hseq.1 $$ [Hlocs Hcmds]
  · iframe Hlocs Hcmds
  imodintro
  -- the `getCmdDesc` loop: each command of the order gets its descriptor (its proposal, read-only
  -- (D16): `proposes`' entry, or a fresh `GPropose`)
  have hnd := sp.syncOrder_nodup M
  -- round 45 (plan R8.2 (9), D55 (2)): `getCmdDesc` takes the reader bundle and the ballot share
  ihave Hrdr : swift.runReader rp n.γdl $$ [Hrdd]
  · iunfold swift.runReader; iexists _; iframe Hdmr Hrdd
  ihave HG : (∃ (j : w64) (cv : swift.CommandId) (pM R : GMap swift.CommandId Loc),
      "i" ∷ i_ptr ↦ j ∗ "cmdId" ∷ cmdId_ptr ↦ cv ∗
      "Hrdr" ∷ swift.runReader rp n.γdl ∗
      "Hbal" ∷ typedPointsto (swift.fld rp go!"ballot") bl (DFrac.own (1 : Qp).half.half) ∗
      "Hpm" ∷ v.props ↦$ pM ∗
      "Hpms" ∷ ([∗map] x ↦ gp ∈ pM, ∃ c, swift.propIs γ gp (toCmdId x) c) ∗
      "HEp" ∷ EpS M ((sp.syncOrder M).take (sint.nat j)) ∗
      "Hrows" ∷ ([∗list] y ∈ (sp.syncOrder M).drop (sint.nat j), swift.claimTok (n.sn N r).γcl (b', y) .sync) ∗
      "%HpM" ∷ ⌜∀ x, toCmdId x ∉ (sp.syncOrder M).take (sint.nat j) →
        pM !! x = pM1 !! x ∧ R !! x = pM1 !! x⌝ ∗
      "%HpS" ∷ ⌜∀ y ∈ (sp.syncOrder M).take (sint.nat j), (pM !! ofCmdId y).isSome⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len⌝ : IProp netDistGF)
    $$ [i cmdId Hrdr Hbal Hpm Hpms HEp Hrows]
  · iexists (W64 0), _, pM1, pM1
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    ipureintro
    refine ⟨fun _ _ => by simp, fun _ h => by simp at h, by decide, by word⟩
  wp_for HG
  wp_if_destruct
  · replace Hif : sint.Z j < sint.Z osl.len := by simpa using Hif
    have hjO : sint.nat j < (sp.syncOrder M).length := by
      have := Hosll.1; simp at this; rw [this]; word
    obtain ⟨y, hy⟩ : ∃ y, (sp.syncOrder M)[sint.nat j]? = some y :=
      ⟨_, List.getElem?_eq_getElem hjO⟩
    rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len from ⟨Hj.1, Hif⟩)]
    wp_apply (wp_load_slice_index (V := swift.CommandId) osl (sint.Z j) _ _ (ofCmdId y) Hj.1)
      $$ [Hosl] as Hosl
    · iframe; ipureintro
      rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_map, hy]; rfl
    try wp_auto
    have hyt : y ∉ (sp.syncOrder M).take (sint.nat j) :=
      github_com.orcaman.concurrent_map.not_mem_take_of_nodup _ (sint.nat j) y hnd hy
    have htake : (sp.syncOrder M).take (sint.nat (j + W64 1)) =
        (sp.syncOrder M).take (sint.nat j) ++ [y] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hy]; rfl
    have hdrop : (sp.syncOrder M).drop (sint.nat j) =
        y :: (sp.syncOrder M).drop (sint.nat (j + W64 1)) := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.drop_eq_getElem_cons hjO]
      congr
      exact Option.some.inj (by rw [← List.getElem?_eq_getElem hjO]; exact hy)
    rw [hdrop]
    icases BigSepL.bigSepL_cons.1 $$ Hrows with ⟨Hrow1, Hrows⟩
    -- `y`'s entry in the `MSync`
    obtain ⟨q, hqM, hqy⟩ : ∃ q ∈ M, q.1 = y := by
      have := sp.syncOrder_mem M y (List.mem_of_getElem? hy)
      obtain ⟨q, hq, h⟩ := List.mem_map.mp this
      exact ⟨q, hq, h⟩
    obtain ⟨iq, hiq⟩ := List.mem_iff_getElem?.mp hqM
    icases (BigSepL.bigSepL_lookup hiq) $$ HMs with ⟨%vs1, %dl1, %Hql1, #Hvs1, #Hdl1⟩
    ihave #Hcq := (BigSepL.bigSepL_lookup hiq) $$ Hcmds
    ihave #Hlq := (BigSepL.bigSepL_lookup hy) $$ Hlocs
    ihave #Haq := (BigSepL.bigSepL_lookup hy) $$ Haccs
    subst hqy
    have hxy : toCmdId (ofCmdId q.1) = q.1 := toCmdId_ofCmdId q.1
    -- `propose, exists := r.proposes[cmdId]`
    wp_apply wp_map_lookup2 $$ [$Hpm] as Hpm
    try wp_auto
    have hyx : toCmdId (ofCmdId q.1) ∉ (sp.syncOrder M).take (sint.nat j) := by rw [hxy]; exact hyt
    obtain ⟨hpx, hRx⟩ := HpM (ofCmdId q.1) hyx
    wp_join iprop(∃ (gp : Loc) (pM' R' : GMap swift.CommandId Loc),
        propose_ptr ↦ gp ∗ cmdId_ptr ↦ ofCmdId q.1 ∗ swift.fld rp go!"proposes" ↦ v.props ∗
        v.props ↦$ pM' ∗
        ([∗map] x ↦ gp ∈ pM', ∃ c, swift.propIs γ gp (toCmdId x) c) ∗
        swift.propIs γ gp q.1 q.2.1 ∗
        ⌜(∀ x, toCmdId x ∉ (sp.syncOrder M).take (sint.nat j) ++ [q.1] →
            pM' !! x = pM1 !! x ∧ R' !! x = pM1 !! x) ∧
          ∀ y ∈ (sp.syncOrder M).take (sint.nat j) ++ [q.1], (pM' !! ofCmdId y).isSome⌝)
      with [propose cmdId Hpr Hpm Hpms]
      as ⟨%gp, %pM', %R', propose, cmdId, Hpr, Hpm, Hpms, #Hgp, %HpM'⟩
    · -- already in `proposes`: its proposal (read-only, D16)
      obtain ⟨gp, hgp⟩ := Option.isSome_iff_exists.mp Hif
      rw [hgp]; simp only [Option.getD_some]
      ihave #Hpall := Hpms
      ihave ⟨%c', #Hh⟩ := (BigSepM.bigSepM_lookup (Φ := fun x gp =>
        iprop(∃ c, swift.propIs γ gp (toCmdId x) c)) hgp) $$ Hpall
      rw [hxy] at *
      ihave #Hh2 := swift.propIs_cmd γ gp q.1 c' q.2.1 $$ [Hh]
      · iframe Hh Hcq
      try wp_auto
      iexists gp, pM, GMap.delete (ofCmdId q.1) R
      iframe
      iframe Hh2
      isplitl []
      · iexact Hpall
      ipureintro
      constructor
      · intro x hx
        have hx1 : toCmdId x ∉ (sp.syncOrder M).take (sint.nat j) := fun h => hx (List.mem_append_left _ h)
        have hx2 : ofCmdId q.1 ≠ x := by
          intro h; apply hx; rw [← h, toCmdId_ofCmdId]; exact List.mem_append_right _ (List.mem_singleton_self _)
        rw [GMap.lookup_delete_ne _ hx2]
        exact HpM x hx1
      · intro y' hy'
        rcases List.mem_append.mp hy' with h | h
        · exact HpS y' h
        · rw [List.mem_singleton.mp h, hgp]; rfl
    · -- a fresh proposal
      have hnone : pM !! ofCmdId q.1 = none := by
        cases h : pM !! ofCmdId q.1
        · rfl
        · rw [h] at Hif; simp at Hif
      ihave ⟨cmdId, %Hcnn⟩ := typedPointsto_not_null_dup _ _ _ $$ cmdId
      iStructNamedPrefix cmdId "C"
      try wp_auto
      ihave cmdId := typedPointsto_combine cmdId_ptr (ofCmdId q.1) _ Hcnn $$ [CSeqNum CClientId]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      wp_apply (wp_map_lookup1 _ _ cm cmM (ofCmdId q.1)) $$ Hcm as -
      rw [Hql1.1]
      simp only [Option.getD_some]
      try wp_auto
      ipersist «$r0»
      iapply fupd_wp
      imod (cmdIs_wf γ γc γm γl q.1 q.2.1) $$ [Hinv Hcq] with %Hwf
      · iframe Hinv Hcq
      imod swift.propIs_new γ «$r0_ptr» «$v0_ptr» q.1 q.2.1 vs1 null null [] 0 Hwf
        $$ [«$v0»] with #Hh1
      · iframe «$r0» «$v0» Hvs1 Hcq
      imodintro
      wp_apply wp_mapInsert $$ [$Hpm] as Hpm
      try wp_auto
      try wp_join_done
      iexists «$r0_ptr», <[ofCmdId q.1 := «$r0_ptr»]> pM, R
      iframe
      iframe Hh1
      isplitl [Hpms]
      · iapply (BigSepM.bigSepM_insert hnone).2
        iframe
        iexists q.2.1; rw [hxy]; iexact Hh1
      ipureintro
      constructor
      · intro x hx
        have hx1 : toCmdId x ∉ (sp.syncOrder M).take (sint.nat j) := fun h => hx (List.mem_append_left _ h)
        have hx2 : ofCmdId q.1 ≠ x := by
          intro h; apply hx; rw [← h, toCmdId_ofCmdId]; exact List.mem_append_right _ (List.mem_singleton_self _)
        rw [GMap.lookup_insert_ne _ _ hx2]
        exact HpM x hx1
      · intro y' hy'
        by_cases hyq : ofCmdId q.1 = ofCmdId y'
        · rw [hyq, GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ hyq]
          rcases List.mem_append.mp hy' with h | h
          · exact HpS y' h
          · exact absurd (by rw [List.mem_singleton.mp h]) hyq
    -- `dep := msg.Deps[cmdId]`, `Dep{}` if nil
    wp_apply (wp_map_lookup1 _ _ dp dpM (ofCmdId q.1)) $$ Hdp as -
    rw [Hql1.2]
    simp only [Option.getD_some]
    try wp_auto
    -- round 47 (46-2): `dep` is not nil (`Dep{}` if nil)
    wp_join iprop(∃ dsl' : GoSlice, dep_ptr ↦ dsl' ∗ dsl' ↦*□ (q.2.2.map ofCmdId) ∗
        ⌜dsl' ≠ slice.nil⌝)
      with [dep] as ⟨%dsl', dep, #Hdsl', %Hdslnn⟩
    · ihave %Hdl1l := ownSlice_len _ _ _ $$ Hdl1
      have hnil : q.2.2.map ofCmdId = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [Hdl1l.1]; rfl
      wp_apply wp_slice_literal_nonnull (V := swift.CommandId) []
      isplitr
      · ipureintro; rfl
      iintro %s0 %Hs0nn ⟨Hs0, -⟩
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hs0 with #Hs0
      imodintro
      try wp_auto
      try wp_join_done
      iexists _
      iframe dep
      isplitr
      · rw [hnil]; iexact Hs0
      ipureintro
      intro h
      have := congrArg (fun s : GoSlice => s.ptr) h
      exact Hs0nn (this.trans rfl)
    · try wp_auto
      try wp_join_done
      iexists dl1
      iframe Hdl1
      iframe
      ipureintro; exact Hif
    -- `r.getCmdDesc(cmdId, &syncEntry{propose, msg.Cmds[cmdId], dep}, nil)`
    wp_apply (wp_map_lookup1 _ _ cm cmM (ofCmdId q.1)) $$ Hcm as -
    rw [Hql1.1]
    simp only [Option.getD_some]
    try wp_auto
    wp_alloc se as Hse
    try wp_auto
    -- round 54 (D74 (2), 53-4): the leader's `locLb` of the `MSync`'s sequence (the pre's)
    ihave #HlbLn : sp.locLb γ (sp.leaderOf n.N b') b' (sp.syncSeq M) $$ []
    · rw [HnN]; iexact HlbL
    wp_apply (wp_getCD gp se r b' (sint.nat j) M
      ((sp.syncOrder M).take (sint.nat j)) (ofCmdId q.1) q.2.1 vs1 dsl' q.2.2 bl (1 : Qp).half.half)
      $$ [HEp Hrdr Hbal Hse Hgp Hrow1] as %d ⟨HEp, Hrdr, Hbal⟩
    · rw [hxy]
      iframe HEp Hrdr Hbal Hse Hgp Hrow1 Hvs1 Hdsl' HM Hlq Haq Hrid Hlb HlbLn
      isplitr
      · ipureintro; exact hbl
      ipureintro
      exact ⟨hqM, hy, Hpre.2.2.1, Hdslnn⟩
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, pM', R'
    rw [htake, hxy]
    iframe
    ipureintro
    exact ⟨HpM'.1, HpM'.2, by word, by word⟩
  -- after the loop: every command of the order has its descriptor and is in `proposes`
  replace Hif : ¬ sint.Z j < sint.Z osl.len := by simpa using Hif
  have hjl : sint.nat j = (sp.syncOrder M).length := by
    have := Hosll.1; simp at this
    have : ¬ sint.Z j < sint.Z osl.len := Hif
    word
  rw [hjl, List.take_length] at HpS HpM
  rw [hjl, List.take_length]
  -- round N3 (D65 (2)): `proposes` has only the order's commands (the dropped ones are out, the
  -- kept ones are the `MSync`'s)
  have hprops' : ∀ y, (pM !! ofCmdId y).isSome → y ∈ sp.syncOrder M := by
    intro y hy
    refine Classical.byContradiction fun hn => ?_
    have h1 := (HpM (ofCmdId y) (by rw [toCmdId_ofCmdId]; exact hn)).1
    rw [h1, hpM] at hy
    split at hy
    · rename_i hph
      have := (HMf.2.2 (ofCmdId y)).1 hph
      rw [toCmdId_ofCmdId] at this
      exact hn (sp.syncOrder_complete M HMf.2.1 y this)
    · simp at hy
  try wp_auto
  -- the replica's facts (`Id`, `N`; the sender's context)
  ihave #Hctx3 := Hctx
  iunfold swift.runCtxD at Hctx3
  icases Hctx3 with ⟨%rr3, %me3, %fr3, %lg3, %dm3, #Hrr3, #HisR3, %Hcf3, -, #Hcfg3, -, -, -, -, -⟩
  ihave %Hrr3eq := typedPointsto_agree_wand _ _ _ _ _ $$ Hrr Hrr3
  subst Hrr3eq
  ihave #Hssc2 := Hssc
  iunfold swift.syncSendCtx at Hssc2
  icases Hssc2 with ⟨%me4, #Hsnd, ⟨%sq, %szS, %memS, #HSQ, #HSQq⟩⟩
  iunfold swift.sendCtxN at Hsnd
  icases Hsnd with ⟨%rr4, %s, %γw4, %γs, %csv, #Hrr4, #HisR4, #Hsnd, #Hbag, #Hcs, %Hcodes⟩
  ihave %Hrr4eq := typedPointsto_agree_wand _ _ _ _ _ $$ Hrr Hrr4
  subst Hrr4eq
  ihave #HisR5 := HisR3
  iunfold replica.isReplica at HisR5
  icases HisR5 with ⟨%lgr, %cfgp, %tbl, %pc, %frr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #HId, -, -, -, -, -, #HPC, #Hpcb, -⟩
  ihave #HisR6 := HisR4
  iunfold replica.isReplica at HisR6
  icases HisR6 with ⟨%lgr', %cfgp', %tbl', %pc', %frr', %nid', %ents', %γpc', %pwsl', %alsl', %latsl',
    %pws', %cwm', -, -, -, #HId4, -⟩
  ihave %Hmeq := typedPointsto_agree_wand _ _ _ _ _ $$ HId HId4
  subst Hmeq
  have hN := (⟨Hcf3.2.2.2.1, Hcf3.2.2.2.2.1⟩ : 1 ≤ N ∧ N ≤ 7)
  wp_auto
  wp_apply (swift.Replica.wp_leader wp_Leader rp rr bl _ N hN) $$ [$Hbal $Hrr $HN] as Hbal
  try wp_auto
  -- a follower acknowledges each command of the order to its client (`MLightSlowAck`)
  wp_join iprop(order_ptr ↦ osl ∗ osl ↦* (sp.syncOrder M).map ofCmdId ∗
      typedPointsto (swift.fld rp go!"ballot") bl (DFrac.own (1 : Qp).half.half))
    with [order Hosl Hbal] as ⟨order, Hosl, Hbal⟩
  · have hnl : sp.rid me3 ≠ sp.leaderOf N b' := by
      intro h
      apply Hif
      have h1 := swift.rid_leaderS bl N b' hN hbl hbl0
      rw [← h1] at h
      have hv := replica.quorum.leader_val bl N (by omega) hbl0
      have hN' : sint.Z (W64 (N : Int)) = N := by word
      unfold sp.rid at h
      apply BitVec.eq_of_toInt_eq
      have h2 := Hcf3.2.1
      have h3 : 0 ≤ (BitVec.srem bl (W32 (sint.Z (W64 (N : Int))))).toInt := by
        have hv' : (BitVec.srem bl (W32 (N : Int))).toInt = bl.toInt % (N : Int) := hv
        rw [hN', hv']; exact Int.emod_nonneg _ (by omega)
      have h4 : 0 ≤ me3.toInt := h2
      omega
    ihave #Hcs2 := Hcs
    iStructNamedPrefix Hcs2 "CS"
    ihave HF : (∃ (j2 : w64) (cv : swift.CommandId),
        "i" ∷ i_ptr ↦ j2 ∗ "cmdId" ∷ cmdId_ptr ↦ cv ∗
        "%Hj2" ∷ ⌜0 ≤ sint.Z j2 ∧ sint.Z j2 ≤ sint.Z osl.len⌝ : IProp netDistGF) $$ [i cmdId]
    · iexists (W64 0), _
      iframe
      ipureintro; exact ⟨by decide, by word⟩
    wp_for HF
    wp_if_destruct
    · replace Hif : sint.Z j2 < sint.Z osl.len := by simpa using Hif
      have hjO : sint.nat j2 < (sp.syncOrder M).length := by
        have := Hosll.1; simp at this; rw [this]; word
      obtain ⟨y, hy⟩ : ∃ y, (sp.syncOrder M)[sint.nat j2]? = some y :=
        ⟨_, List.getElem?_eq_getElem hjO⟩
      rw [ite_eq_left (show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z osl.len from ⟨Hj2.1, Hif⟩)]
      wp_apply (wp_load_slice_index (V := swift.CommandId) osl (sint.Z j2) _ _ (ofCmdId y) Hj2.1)
        $$ [Hosl] as Hosl
      · iframe; ipureintro
        rw [show (sint.Z j2).toNat = sint.nat j2 by word, List.getElem?_map, hy]; rfl
      try wp_auto
      rw [MethodUnfold.method_unfold (t := go.GoType.PointerType replica.Sender.ty)
        (m := go!"SendToClient")]
      try wp_auto
      ihave #Hay := (BigSepL.bigSepL_lookup hy) $$ Haccs
      wp_apply (wp_sendc rr γ γc γm γw4 N me3 γs s y.cl
          (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #«$r0_ptr»)
          (.lightSlowAck ⟨me3, bl, y⟩) csv.lightSlowAckRPC'
          iprop(«$r0_ptr» ↦ swift.MLightSlowAck.mk me3 bl (ofCmdId y))) $$ [«$r0»]
      · iframe HisR4 Hbag
        unfold replica.toSend
        isplitl
        · isplitr
          · iapply (hms «$r0_ptr» (swift.MLightSlowAck.mk me3 bl (ofCmdId y)) ⟨me3, bl, y⟩
              ⟨rfl, rfl, by rw [toCmdId_ofCmdId]⟩)
          isplitl [«$r0»]
          · iframe
          isplitr
          · iapply (swift.lsaOk_introS γ γc γm N fr3 lg3 me3 bl y ⟨Hcf3.2.1, hbl0⟩
              (by rw [hbl]; exact hnl))
            iframe Hcfg3; rw [Hcf3.1, hbl]; iexact Hay
          isplitr
          · unfold replica.freeOk; ileft; ipureintro; rfl
          ipureintro; refine ⟨trivial, ?_⟩; rw [Hcodes.2.2.2.1]; rfl
        ipureintro; rfl
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · try wp_auto
      try wp_join_done
  -- the reproposals, each sent to `ProposeChan` by its own goroutine (GAP R-half: both halves)
  ihave %Hrl := ownSlice_len _ _ _ $$ Hrsl
  ihave HR : (∃ (k : w64) (pv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "propose" ∷ propose_ptr ↦ pv ∗
      "Hreps" ∷ ([∗list] gp ∈ gps.drop (sint.nat k), sp.proposeP γ gp) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rsl.len⌝ : IProp netDistGF) $$ [i propose Hreps]
  · iexists (W64 0), _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for HR
  wp_if_destruct
  · have hkO : sint.nat k < gps.length := by rw [Hrl.1]; word
    obtain ⟨gp, hgp⟩ : ∃ gp, gps[sint.nat k]? = some gp := ⟨_, List.getElem?_eq_getElem hkO⟩
    rw [ite_eq_left (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rsl.len from ⟨Hk.1, Hif⟩)]
    wp_apply (wp_load_slice_index (V := Loc) rsl (sint.Z k) _ _ gp Hk.1) $$ [Hrsl] as Hrsl
    · iframe; ipureintro
      rw [show (sint.Z k).toNat = sint.nat k by word, hgp]
    have hdrop : gps.drop (sint.nat k) = gp :: gps.drop (sint.nat (k + W64 1)) := by
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.drop_eq_getElem_cons hkO]
      congr
      exact Option.some.inj (by rw [← List.getElem?_eq_getElem hkO]; exact hgp)
    rw [hdrop]
    icases BigSepL.bigSepL_cons.1 $$ Hreps with ⟨Hp, Hreps⟩
    try wp_auto
    wp_apply wp_fork $$ [Hp]
    · wp_auto
      wp_apply wp_bag_send (t := go.GoType.PointerType replica.defs.GPropose.ty) γpc pc gp
        (sp.proposeP γ) $$ [$Hpcb $Hp]
      itrivial
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  try wp_auto
  -- the four `log.Println`s (`swift.wp_PrintlnT`: each argument's `touch`)
  have tStr : ∀ x : GoString, swift.printable (interface.mkOk go.string #x) :=
    fun x => swift.printable_of_argsWf _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)
  have tI32 : ∀ x : w32, swift.printable (interface.mkOk go.int32 #x) :=
    fun x => swift.printable_of_argsWf _
      (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 x) fmt.ArgsWf.nil)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) [_]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl1 ⟨Hlsl1, -⟩
  wp_auto
  wp_apply (swift.wp_PrintlnT _ _ _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; subst hx
    exact tStr _)) $$ [$Hlsl1] as -
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) [_, _]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl2 ⟨Hlsl2, -⟩
  wp_auto
  wp_apply (swift.wp_PrintlnT _ _ _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact tStr _
    · exact tI32 _)) $$ [$Hlsl2] as -
  try wp_auto
  ihave %HsqF := swift.quorumIs_noFmt sq szS memS $$ HSQq
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) [_, _, _, _]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl3 ⟨Hlsl3, -⟩
  wp_auto
  wp_apply (swift.wp_PrintlnT _ _ _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact tStr _
    · exact swift.wp_touch_noFmt _ (fun ii h => by cases h; exact swift.quorumTy_noFmt)
    · exact tStr _
    · exact swift.wp_touch_noFmt _ HsqF)) $$ [$Hlsl3] as -
  try wp_auto
  ihave #Htm2 := swift.time_init $$ Hpkg
  wp_apply wp_Now $$ [$Htm2] as %tn _
  wp_apply (wp_Sub tn t0) as %dur _
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType []) [_, _]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl4 ⟨Hlsl4, -⟩
  wp_auto
  wp_apply (swift.wp_PrintlnT _ _ _ (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact tStr _
    · exact swift.printable_of_argsWf _ (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int64 _) fmt.ArgsWf.nil))) $$ [$Hlsl4] as -
  try wp_auto
  -- the post: normal operation at `b'` (`sync_runSt`), the new epoch with its descriptors
  ihave Hn1 : (slice.nil ↦* ([] : List swift.CommandId) : IProp netDistGF) $$ []
  · iapply ownSlice_nil
  ihave Hn2 : (ownSliceCap swift.CommandId slice.nil (DFrac.own 1) : IProp netDistGF) $$ []
  · iapply ownSliceCap_nil
  ihave Hrst := swift.sync_runSt γ γv rp N r ld v M0 w b' M bl slice.nil v.props pM km' kM hm' pp' ls
    Hok.1 hcb hbl (fun y hy => HpS y hy) hprops'
    $$ [Hbal Hcb Hstat Hhd Hn1 Hn2 Hpr Hpm Hpms Hk Hks' Hhl Hhm' Hpe Hpp' Hls0 Hw]
  · iframe Hbal Hcb Hhd Hn1 Hn2 Hpr Hk Hks' Hhl Hhm' Hpe Hpp' Hls0 Hw HMapsP HM HlbL Hlocs Hcmds
    isplitl [Hstat]
    · iExactEq Hstat; rfl
    iunfold swift.propsOwn
    iframe
  iapply HΦ
  isplitl [Hrdr]
  · iexact Hrdr
  iright
  iexists _, _
  iframe Hrst HEp
  isplitl
  · iunfold swift.syncFieldsOwnE
    iexists t0, rc2, _, pd'
    iframe
  ipureintro; exact ⟨rfl, rfl, rfl⟩

theorem swift.Replica.handleSync.wp_proof (EpR EpH : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF) (γ : sp.Names) (γc γm γl γw γv γd γe γo : GName) (n : swift.SyncN) (rp rr : Loc)
    (PC : IProp netDistGF)
    (wp_Now : time.Now.spec (GF := netDistGF) (hG := hG))
    (wp_sorted : swift.sortedProposes.specI (hG := hG))
    (wp_IterCbVN : github_com.orcaman.concurrent_map.ConcurrentMap.IterCbVN.spec (GF := netDistGF))
    (wp_Free : replica.mset.MsgSet.Free.specQ (hG := hG))
    (wp_freeDesc : ∀ b, swift.Replica.freeDesc.specI (hG := hG) (DF b))
    (wp_InitState : state.InitState.spec (GF := netDistGF))
    (wp_IterCbV : github_com.orcaman.concurrent_map.ConcurrentMap.IterCbV.spec (GF := netDistGF))
    (wp_RemoveV : github_com.orcaman.concurrent_map.ConcurrentMap.RemoveV.spec (GF := netDistGF))
    (wp_Store : sync.atomic.Bool.Store.spec (GF := netDistGF) (hG := hG))
    (wp_CNew : github_com.orcaman.concurrent_map.NewV.spec (GF := netDistGF))
    (wp_AQ : replica.QuorumSystem.AQ.spec (hG := hG))
    -- GAP H-size: sv-swc's restated `NewReplyChan.specI` (not landed): `historySize` not taken
    (wp_NRC : swift.NewReplyChan.specIH (hG := hG))
    (wp_syncOrder : swift.syncOrder.specI (hG := hG))
    (wp_keysOf : swift.keysOf.specI (hG := hG))
    (wp_newLKI : swift.lki.newLightKeyInfo.spec (hG := hG))
    (wp_lkiAdd : swift.lki.lightKeyInfo.add.spec (hG := hG))
    (EpS_start : ∀ (N r b' : Nat) (M : sp.SyncMsg), 0 < b' →
      swift.syncCtx γ N r n rp ∗ □ PC ∗ swift.epFresh γ γc γm n γe γd rp rr b' ⊢ |={⊤}=> EpS M [])
    (wp_stop : swift.replyChan.stop.specI (hG := hG) EpR EpH rp)
    (wp_stopD : swift.Replica.stopDescs.specI (hG := hG) EpH γ n γe γd DF PS rr rp)
    (wp_getCD : swift.Replica.getCmdDesc.syncSpecI (hG := hG) EpS γ n.γcl n.γdl rp n.N)
    (wp_Leader : replica.Leader.spec (hG := hG))
    (wp_sendc : replica.Sender.SendToClient.spec (hG := hG))
    (hms : ∀ (l : Loc) (sa : swift.MLightSlowAck) (s : sp.SlowAck), swift.slowAckRepr sa s →
      ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l)
        (.lightSlowAck s) iprop(l ↦ sa))
    (wp_Sub : time.Time.Sub.spec (GF := netDistGF) (hG := hG))
    -- GAP C-wf (§18 round 14): registered commands are well formed (`Cmd.wf`, as `propIs`
    -- requires); an invariant fact not yet in `sp.inv`
    (cmdIs_wf : ∀ (γ : sp.Names) (γc γm γl : GName) (x : sp.CmdId) (c : sp.Cmd),
      sp.inv γ γc γm γl ∗ sp.cmdIs γ x c ⊢ |={⊤}=> ⌜c.wf⌝) :
    swift.Replica.handleSync.specI (hG := hG) EpR EpS DF PS γ γc γm γl γw γv γd γe γo n rp rr PC :=
  (swift.Replica.handleSync.wp_proofR EpR EpH EpS DF PS γ γc γm γl γw γv γd γe γo n rp rr PC wp_Now wp_sorted wp_IterCbVN wp_Free wp_freeDesc wp_InitState wp_IterCbV wp_RemoveV wp_Store wp_CNew wp_AQ wp_NRC wp_syncOrder wp_keysOf wp_newLKI wp_lkiAdd EpS_start wp_stop wp_stopD wp_getCD wp_Leader wp_sendc hms wp_Sub cmdIs_wf)

end proof

end Perennial.github_com.imdea_software.swiftpaxos
