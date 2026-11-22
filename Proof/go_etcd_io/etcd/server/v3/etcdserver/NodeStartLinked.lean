/-
The compositions of `NodeStart.lean` (`raftNode_of_StartNode`, `raftNode_of_RestartNode`), which use
raft's linked `MemoryStorage.wp_Append` (through `isRNMemStor_of_memstorage`,
`NodeBridgeLinked.lean`): moved out of `NodeStart.lean` (2026-11-18) so that the server's
invariants, which import it for `NodeStartSpec`, import no linked result (CLAUDE.md, "Import
tiers").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplaySeed
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.replayTermsFromStorage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeBridgeLinked
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeStartLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section compose
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
/-- **The composition** (see `NodeStartSpec` and the file header): from
`bootstrappedRaft.newRaftNode.spec` (through it the node API's `StartNode`) and the node API's node
specs (for its contract, `isRaftNodeIfc_of_isNode`), at the cluster's storage model. -/
theorem raftNode_of_StartNode
    (wp_bnr : bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG))
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Ready : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Advance.spec (GF := GF) (hG := hG))
    (wp_Tick : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Tick.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Stop.spec (GF := GF) (hG := hG))
    (wp_ReadIndex : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReadIndex.spec (GF := GF) (hG := hG))
    (wp_Step : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Step.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (wp_Propose : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Propose.spec (GF := GF) (hG := hG))
    (wp_ApplyConfChange : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ApplyConfChange.spec (GF := GF) (hG := hG)) :
    NodeStartSpec (GF := GF) := by
  intro γr E b ss wal cl sd dq bv cv lok γs ν pv ps ctxs issued
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro %Φ Hpre HΦ
  iNamed Hpre
  obtain ⟨Hcfg, Hhb, Hnodup, H0, Hpslen, Hvs, Hwal, Hfit, HtrC⟩ := Hraft
  imod (dghostVar_alloc (GF := GF) (A := GName) default) with ⟨%pin, HpinW⟩
  ihave Hbs := srvMem_bootStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
      wp_Entries γr bv.storage' γs E.γr.cursor pin
      (fun K => iprop(memStorInvT bv.storage' γs γr.cl K (srvStoredOrigin γr.cl E.γr.cursor pin 0) ∗
        memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)))) HtrC Hγsz
      $$ [Hfresh Hmeta Hend]
  · iframe Hreg Hlock Hfresh Hmeta Hlog0 Hend
    iintro %K Hi Hm
    iframe Hi Hm
  icases Hboot with ⟨#Hnboot, HrS, Hvac⟩
  iapply wp_fupd
  wp_apply (wp_bnr E γr b ss wal cl sd dq bv cv lok γs [] ν pv ps ctxs
    (fun K => iprop(memStorInvT bv.storage' γs γr.cl K (srvStoredOrigin γr.cl E.γr.cursor pin 0) ∗
      memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)))) .fresh (fun sv => iprop(snapshotValid γr.cl sv ∗ (srvStoredOrigin γr.cl E.γr.cursor pin 0) sv)) (fun _ => by iintro ⟨H, -⟩; iexact H))
    $$ [Hb Hc Hbs Hpeers HrS Hvac]
    as %r Hpost
  · iframe #; iframe Hb Hc Hpeers
    isplitr
    · ipureintro; exact ⟨Hhb, Hwal, HtrC⟩
    simp only [rnBootPre]
    isplitr
    · ipureintro; exact Hcfg
    isplitl [Hbs]
    · iExactEq Hbs; rfl
    isplitr
    · iExactEq Hnboot; rfl
    isplitl [Hvac]
    · iExactEq Hvac; rfl
    iExactEq HrS; rfl
  icases Hpost with ⟨%n, %γw, %f, %st, %terms, %Hnames, #Hnode, Hrun, #Hpin, Hbpost, #Hidri, #Hsti, Hrd1, Hrd2,
    #Hseed, Hbuilt, Hb, Hpeers, ⟨#Hminv, Hmeta⟩⟩
  simp only [rnBootPost, RNBoot.P]
  icases Hbpost with ⟨#Hsfresh, Hdrv, HrS, Hncfg⟩
  simp only [RNBoot.a0, RNBoot.t0, RNBoot.commit0, RNBoot.snap0] at Hnames
  obtain ⟨Hwnode, Hwid, Hwnl, Hwpre, Hwms, Hwγs, Hwwal, Hwss, Hwa0, Hwt0, Hwc0, Hws0⟩ := Hnames
  imod dghostVar_update n.installs pin default $$ HpinW with HpinW
  imod dghostVar_persist pin 1 n.installs $$ HpinW with #Hloc
  ihave #Hattach : srvAttachedMem bv.storage' γs γr.cl γw.key E.γr.cursor γw.nl γw.snap0 $$ []
  · rw [Hwnl, Hws0]
    iunfold srvAttachedMem
    iexists pin
    iframe Hloc Hpin Hminv
  iunfold rnBuilt at Hbuilt
  iNamed Hbuilt
  obtain ⟨Hrvlg, Hrvcfg⟩ := Hrv
  -- the bridges
  ihave #Hfits' : rnLogFits γw $$ []
  · iunfold rnLogFits; ipureintro; rw [Hwnode]; exact Hfit
  ihave #Hreg' : rnMemStorReg γw $$ []
  · unfold rnMemStorReg RNNames.reg; rw [Hwms, Hwγs, Hwnode]; iexact Hreg
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hmsi : isRNMemStor γw γw.ms $$ []
  · iapply isRNMemStor_of_memstorage γw
    iframe Hpraft Hreg'
    rw [Hwms, Hwγs]; iexact Hlock
  ihave #Hisnode : rnIsNode γw $$ []
  · unfold rnIsNode; rw [Hwnode, Hwid, Hwnl]; iexact Hnode
  -- the running token's halves
  icases ((nodeRunning_fractional n γr.cl srvClusterN).fractional (1 : Qp).half
      (1 : Qp).half).1 $$ [Hrun] with ⟨Hrun1, Hrun2⟩
  · rw [Qp.half_add_half]; iexact Hrun
  -- the tokens
  ihave ⟨Hloop, Happly⟩ := rnToks_of_start γw Hwpre Hwa0 Hwt0 Hwc0 Hws0
      (by
        rw [Hwnode]
        unfold SrvRaft.cfg
        rw [Hvs]
        refine srvCfgOk_nil _ (fun h0 => H0 ((GMap.elem_of_list_to_set _ _).1 h0)) ?_
        rw [GMap.size_list_to_set ps Hnodup]
        omega)
    $$ [Hdrv HrS Hncfg Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok]
  · rw [Hwnode, Hwnl, Hwms, Hwid, Hwwal]
    iframe Hdrv HrS Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok
    unfold SrvRaft.cfg
    rw [Hvs]
    iexact Hncfg
  imodintro
  iapply HΦ
  iexists γw, rv
  isplitr
  · ipureintro
    refine ⟨Hwnode, Hwid, Hwpre, Hwms, Hwγs, Hwwal, Hwss, Hwa0, Hws0, Hrvlg, ?_, ?_, ?_, ?_⟩ <;> rw [Hrvcfg]
    all_goals first | rfl | simp only [rnNodeIface, Hwnl]
  ihave #Hsti' : isWalStorage rv.raftNodeConfig'.storage' γw.wal.h γw.ss $$ []
  · rw [Hrvcfg]; iexact Hsti
  ihave Hrd1' : walStorRd rv.raftNodeConfig'.storage' γw.wal.h $$ [Hrd1]
  · rw [Hrvcfg]; iexact Hrd1
  ihave Hrd2' : walStorRd rv.raftNodeConfig'.storage' γw.wal.h $$ [Hrd2]
  · rw [Hrvcfg]; iexact Hrd2
  iframe Hsti' Hrd1' Hrd2' Hr Hmu Hloop Happly Hb Hpeers Hattach Hmeta Hsc
  isplitr
  · iapply rnStepIfc_of_isNode γw (wp_Step γw.node) (wp_ReportUnreachable γw.node)
      (wp_ReportSnapshot γw.node) (by rw [Hwnode]; exact HtrC)
    iframe Hpkg Hisnode
  isplitr
  · rw [Hwnl]; iexact Hsfresh
  isplitl [Hrun2]
  · rw [Hwnode, Hwnl]; iexact Hrun2
  -- the installer
  iintro %a %s %tr #Henv' #Hcommi #Hrdi #Hfix Htrf Hlts Hreplay #Htri Hmu' %Hb30
  ihave #Hrsb : rnReadStateBridge E γw $$ []
  · iapply rnReadStateBridge_of_raft E γw $$ Henv'
  ihave #Hni : isRaftNodeIfc E γw (rnNodeIface γw) $$ []
  · iapply isRaftNodeIfc_of_isNode E γw s issued (wp_Ready γw.node) (wp_Advance γw.node)
      (wp_Tick γw.node) (wp_Stop γw.node) (wp_ReadIndex γw.node)
      (wp_ApplyConfChange γw.node)
    iframe Hpkg Henv' Hisnode Hcommi Hreg' Hrdi
  ihave #Hlinv : srvRaftLogInv E.γr.raft $$ []
  · iunfold rnEnvOk at Henv'
    icases Henv' with ⟨-, -, -, #H, -⟩
    iexact H
  ihave #Hprop : raftPropose E.γr.raft (rnNodeIface γw) $$ []
  · iapply raftPropose_of_isNode E γw (wp_Propose γw.node)
    iframe Hpkg Henv' Hisnode Hlinv
  ihave #Hfix' : rnFixed a
      { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } $$ []
  · simp only [rnFixed]
    iexact Hfix
  have hn0 : ({ rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } :
      raftNode).raftNodeConfig'.Node' =
      interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.node.ty) #γw.nl.loc := by
    simp only [Hrvcfg, rnNodeIface, Hwnl]
  ihave #Hstate : rnReplayState γw rv.raftNodeConfig'.initialReplayTerms' γw.snap0 $$ []
  · rw [Hrvcfg]
    iunfold rnReplayState
    iexists ([] : List replayTermRun)
    isplitr
    · iExactEq Hseed; rfl
    ipureintro; simp [Hwa0, replayPending, replayLayout]
  imod (isRaftNode_of_rnParts E γw a
    { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } hn0 Hb30)
    $$ [Htrf Hlts Hreplay Hmu' Hdtok] with ⟨#Hrn, Hdone, #Hnodef, #Htrf⟩
  · iframe Hpkg Henv' Hfits' Hrsb Hreg' Hfix' Htrf Hlts Hreplay Hmu' Hdtok Hstate
    isplitr
    · iunfold rnRestartOk; ileft; ipureintro; exact ⟨Hwa0, Hwt0, Hwc0, Hws0⟩
    simp only [Hrvcfg]
    iframe Hidri Hsti Htri Hmsi
    isplitr
    · -- the node's contract, at the config's `Node` field
      rw [← Hwnl]
      iexact Hni
    isplitr
    · ipureintro; exact Hwms.symm
    isplitr
    · rw [Hwwal, Hwnode]; iexact Hdur
    -- the components are the same (`transport` is no component)
    iunfold rnParts at Hparts
    iunfold rnParts
    iNamed Hparts
    simp only [named]
    iframe #
  imodintro
  iframe Hrn Hdone Htrf Hprop
  have hn : rnNodeIface γw =
      ({ rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } : raftNode).raftNodeConfig'.Node' := by
    simp only [Hrvcfg, rnNodeIface, Hwnl]
  rw [hn]
  iexact Hnodef

theorem raftNode_of_StartNode_law_holds : raftNode_of_StartNode.law (GF := GF) (hG := hG) :=
  raftNode_of_StartNode


set_option maxHeartbeats 0 in
/-- (restart S3 item 8, 2026-11-11) **The composition at a restart** (see `NodeStartSpecR`): from
`bootstrappedRaft.newRaftNode.spec` at `.restart` (through it the node API's `RestartNode`) and the
node API's node specs, as `raftNode_of_StartNode`. -/
theorem raftNode_of_RestartNode
    (wp_bnr : bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG))
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Ready : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Advance.spec (GF := GF) (hG := hG))
    (wp_Tick : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Tick.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Stop.spec (GF := GF) (hG := hG))
    (wp_ReadIndex : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReadIndex.spec (GF := GF) (hG := hG))
    (wp_Step : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Step.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (wp_Propose : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Propose.spec (GF := GF) (hG := hG))
    (wp_ApplyConfChange : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ApplyConfChange.spec (GF := GF) (hG := hG)) :
    NodeStartSpecR (GF := GF) := by
  intro γr E b ss wal cl sd dq bv cv lok γs ν pv ctxs issued σ cs S m A₀
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro %Φ Hpre HΦ
  iNamed Hpre
  obtain ⟨Hcfg, Hhb, Hwal, Hfit, H0, Hsz, Hba, Hac, Hboot, Hhold, Hterm, Hcs, Hcsb, Hnsm⟩ := Hraft
  have Hbc : σ.b ≤ σ.commit := Nat.le_trans Hba Hac
  -- the cluster untraced (`srvClusterOk`'s, in the server's raft-log invariant)
  ihave %HtrC : ⌜Cluster.trace γr.cl = none⌝ $$ []
  · iunfold srvRaftLogInv at Hlinv
    icases Hlinv with ⟨-, #Hclok, -⟩
    iapply srvClusterOk_untraced (⟨γr, [], W64 0⟩ : ServerRaftNames) $$ Hclok
  -- the configuration at the backend's index the voters' (Q39)
  imod srv_confAt_eq_simple ⟨γr, [], W64 0⟩ (srvLE ⟨γr, [], W64 0⟩ A₀) A₀.length m
      (by simp [srvLE]) ⊤ (by simp) (by simp) $$ [$Hlinv $Hconf] with %Hm
  · iunfold srvRLogLb at HA0; icases HA0 with ⟨#H, -⟩; iexact H
  subst Hm
  -- the restarted storage's snapshot valid (D4) and its persistent part, for the frozen terms
  imod walSnapCS_valid ⟨γr, [], W64 0⟩ σ cs ⊤ (by simp) (by simp) Hterm Hcs Hcsb $$ [$Hlinv $Hcert]
    with Hval
  ihave %Hlt := restart_lastTerm γr A₀ σ Hba Hterm $$ [$HA0 $Hcert]
  iunfold memStorRestarted at Hrest
  icases Hrest with ⟨Hfresh, Hmeta, #Hcp, #He0, Hsn, Hents, Hend⟩
  ihave #Hfz : srvFrozenTerms γs 1 (A₀.take σ.b) $$ []
  · have hlen : (A₀.take σ.b).length = σ.b := by simp; omega
    iapply srvFrozenTerms_restart γs (A₀.take σ.b) (memDummy (walSnapCS σ cs)) Hlt
    rw [hlen]
    iframe Hcp He0
  imod (dghostVar_alloc (GF := GF) (A := GName) default) with ⟨%pin, HpinW⟩
  ihave #Himage : isCommittedLogLb γr.cl (A₀.map EntryModel.toLE) $$ []
  · iunfold srvRLogLb at HA0
    icases HA0 with ⟨#Himage, -⟩
    iExactEq Himage
    simp [srvLE]
  iapply wp_fupd
  imod replaySeed_facts γr.cl cv.ID' srvClusterN S σ (A₀.map EntryModel.toLE)
      Hhold (by simp; exact Nat.le_trans Hac Hhold.2.2.2.2.2.2.2.1) $$ [$Hclu $HrS $Himage]
    with ⟨HrS, %hseed⟩
  ihave Hrest : memStorRestarted bv.storage' γs σ cs $$ [Hfresh Hmeta Hsn Hents Hend]
  · iunfold memStorRestarted
    iframe Hfresh Hmeta Hcp He0 Hsn Hents Hend
  wp_apply (wp_bnr E γr b ss wal cl sd dq bv cv lok γs [] ν pv [] ctxs
    (fun K => iprop(memStorInvT bv.storage' γs γr.cl K (srvStoredOrigin γr.cl E.γr.cursor pin σ.b) ∗ memStorMeta bv.storage' γs σ.hs ∗
      memSnapNone γs (walSnapCS σ cs)))
    (.restart σ cs S A₀.length (Membership.simple γr.cfg) A₀) (fun sv => iprop(snapshotValid γr.cl sv ∗ (srvStoredOrigin γr.cl E.γr.cursor pin σ.b) sv)) (fun _ => by iintro ⟨H, -⟩; iexact H))
    $$ [Hb Hc Hrest Hval Hpeers HrS Hvac]
    as %r Hpost
  · iframe #; iframe Hb Hc Hpeers
    isplitr
    · ipureintro; exact ⟨Hhb, Hwal, HtrC⟩
    simp only [rnBootPre]
    isplitr
    · ipureintro; exact ⟨Hcfg, Hba, Hac, Hboot, Hcs, Hhold, Hnsm⟩
    isplitl [Hrest Hval]
    · iintro %Ψ HΨ
      wp_apply replayTermsFromStorage.wp_proof wp_FirstIndex wp_LastIndex wp_Entries
          RaftLink.entryGetIndex RaftLink.entryGetTerm bv.storage' γs σ cs (hseed.1.imp fun h => h.1)
          $$ [$Hpkg $Hlock $Hrest] as %out ⟨Hrest, #Hterms⟩
      iapply HΨ
      iframe Hterms
      iapply srvMem_restartStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
        wp_Entries γr bv.storage' γs E.γr.cursor pin σ cs 0 _ Hbc HtrC Hγsz Hnsm
      iframe Hreg Hlock Hrest Hval
      iintro %K Hi Hm Hn
      iframe Hi Hm Hn
    isplitr
    · iExactEq Hclu; rfl
    isplitr
    · iExactEq Hrf; rfl
    isplitl [Hvac]
    · iExactEq Hvac; rfl
    isplitl [HrS]
    · iExactEq HrS; rfl
    iExactEq Hconf; rfl
  icases Hpost with ⟨%n, %γw, %f, %st, %terms, %Hnames, #Hnode, Hrun, #Hpin, Hbpost, #Hidri, #Hsti, Hrd1, Hrd2,
    #Hseed, Hbuilt, Hb, Hpeers, ⟨#Hminv, Hmeta, Hsnone⟩⟩
  simp only [rnBootPost, RNBoot.P]
  icases Hbpost with ⟨%l, #Hl, %Hll, Hdrv, HrS, Hncfg⟩
  simp only [RNBoot.a0, RNBoot.t0, RNBoot.commit0, RNBoot.snap0] at Hnames
  obtain ⟨Hwnode, Hwid, Hwnl, Hwpre, Hwms, Hwγs, Hwwal, Hwss, Hwa0, Hwt0, Hwc0, Hws0⟩ := Hnames
  imod dghostVar_update n.installs pin default $$ HpinW with HpinW
  imod dghostVar_persist pin 1 n.installs $$ HpinW with #Hloc
  ihave #Hattach : srvAttachedMem bv.storage' γs γr.cl γw.key E.γr.cursor γw.nl γw.snap0 $$ []
  · rw [Hwnl, Hws0]
    iunfold srvAttachedMem
    iexists pin
    iframe Hloc Hpin Hminv
  -- the driver's delivered log is the backend's up to the base (committed logs agree)
  ihave %Hleq : ⌜l = srvLE ⟨γr, [], W64 0⟩ (A₀.take σ.b)⌝ $$ []
  · iunfold srvRLogLb at HA0
    icases HA0 with ⟨#HAc, -⟩
    icases isCommittedLogLb_agree γr.cl l (srvLE ⟨γr, [], W64 0⟩ A₀) $$ [Hl HAc] with %Hag
    · iframe Hl HAc
    ipureintro
    have hSL : (srvLE ⟨γr, [], W64 0⟩ A₀).length = A₀.length := by simp [srvLE]
    have e : srvLE ⟨γr, [], W64 0⟩ (A₀.take σ.b) = (srvLE ⟨γr, [], W64 0⟩ A₀).take l.length := by
      rw [Hll]; simp [srvLE, List.map_take]
    rw [e]
    rcases Hag with h | h
    · exact List.prefix_iff_eq_take.1 h
    · have := h.length_le
      rw [hSL] at this
      have heq : srvLE ⟨γr, [], W64 0⟩ A₀ = l := List.IsPrefix.eq_of_length h (by omega)
      rw [heq, List.take_length]
  subst Hleq
  iunfold rnBuilt at Hbuilt
  iNamed Hbuilt
  obtain ⟨Hrvlg, Hrvcfg⟩ := Hrv
  have Hsrv : γw.srv = ⟨γr, [], W64 0⟩ := by
    unfold RNNames.srv; rw [Hwnode, Hwpre]
  -- the bridges
  ihave #Hfits' : rnLogFits γw $$ []
  · iunfold rnLogFits; ipureintro; rw [Hwnode]; exact Hfit
  ihave #Hreg' : rnMemStorReg γw $$ []
  · unfold rnMemStorReg RNNames.reg; rw [Hwms, Hwγs, Hwnode]; iexact Hreg
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hmsi : isRNMemStor γw γw.ms $$ []
  · iapply isRNMemStor_of_memstorage γw
    iframe Hpraft Hreg'
    rw [Hwms, Hwγs]; iexact Hlock
  ihave #Hisnode : rnIsNode γw $$ []
  · unfold rnIsNode; rw [Hwnode, Hwid, Hwnl]; iexact Hnode
  icases ((nodeRunning_fractional n γr.cl srvClusterN).fractional (1 : Qp).half
      (1 : Qp).half).1 $$ [Hrun] with ⟨Hrun1, Hrun2⟩
  · rw [Qp.half_add_half]; iexact Hrun
  -- the tokens at `P`
  ihave %HAidx : ⌜srvIdxOkW (W64 0) A₀⌝ $$ []
  · iunfold srvRLogLb at HA0; icases HA0 with ⟨-, %h⟩; ipureintro; exact h
  have hidx : srvIdxOkW (W64 0) (A₀.take σ.b) :=
    srvIdxOkW_prefix _ _ _ HAidx (List.take_prefix _ _)
  have hghost : rnGhost γw (A₀.take σ.b) = A₀ := by
    unfold rnGhost
    rw [Hwpre, Hwa0, List.nil_append, List.length_take, Nat.min_eq_left Hba, List.take_append_drop]
  have hcfgv : srvCfgOk γw.node.cfg (rnGhost γw (A₀.take σ.b))
      ⟨A₀.length, Membership.simple γr.cfg⟩ := by
    rw [hghost, Hwnode]
    exact ⟨Nat.le_refl _, fun _ _ h1 h2 _ => absurd h2 (by simp; omega),
      ⟨γr.cfg, rfl, fun _ h => h, fun _ h1 h2 => absurd h1 h2, H0, Hsz⟩⟩
  ihave ⟨Hloop, Happly⟩ := rnToks_of_restart γw (A₀.take σ.b) σ.hs S
      ⟨A₀.length, Membership.simple γr.cfg⟩ Hwpre hidx (by rw [Hwc0]; exact Nat.le_refl _)
      (by simp [rnLogOf, Hwpre, Hws0, Nat.min_eq_left Hba]) hcfgv
    $$ [Hdrv HrS Hncfg Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok]
  · rw [Hsrv, Hwnode, Hwnl, Hwms, Hwid, Hwwal, Hwγs]
    iframe Hdrv HrS Hncfg Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok Hfz
  imodintro
  iapply HΦ
  iexists γw, rv
  isplitr
  · ipureintro
    refine ⟨Hwnode, Hwid, Hwpre, Hwms, Hwγs, Hwwal, Hwss, Hwa0, Hwt0, Hwc0, Hws0, Hrvlg, ?_, ?_, ?_, ?_⟩ <;>
      rw [Hrvcfg]
    all_goals first | rfl | simp only [rnNodeIface, Hwnl]
  ihave #Hsti' : isWalStorage rv.raftNodeConfig'.storage' γw.wal.h γw.ss $$ []
  · rw [Hrvcfg]; iexact Hsti
  ihave Hrd1' : walStorRd rv.raftNodeConfig'.storage' γw.wal.h $$ [Hrd1]
  · rw [Hrvcfg]; iexact Hrd1
  ihave Hrd2' : walStorRd rv.raftNodeConfig'.storage' γw.wal.h $$ [Hrd2]
  · rw [Hrvcfg]; iexact Hrd2
  iframe Hsti' Hrd1' Hrd2' Hr Hmu Hloop Happly Hb Hpeers Hattach Hmeta Hsnone Hsc
  isplitr
  · iapply rnStepIfc_of_isNode γw (wp_Step γw.node) (wp_ReportUnreachable γw.node)
      (wp_ReportSnapshot γw.node) (by rw [Hwnode]; exact HtrC)
    iframe Hpkg Hisnode
  isplitl [Hrun2]
  · rw [Hwnode, Hwnl]; iexact Hrun2
  -- the installer
  iintro %a %s %tr #Henv' #Hcommi #Hrdi #Hfix Htrf Hlts Hreplay #Htri Hmu' %Hb30
  ihave #Hrsb : rnReadStateBridge E γw $$ []
  · iapply rnReadStateBridge_of_raft E γw $$ Henv'
  ihave #Hni : isRaftNodeIfc E γw (rnNodeIface γw) $$ []
  · iapply isRaftNodeIfc_of_isNode E γw s issued (wp_Ready γw.node) (wp_Advance γw.node)
      (wp_Tick γw.node) (wp_Stop γw.node) (wp_ReadIndex γw.node)
      (wp_ApplyConfChange γw.node)
    iframe Hpkg Henv' Hisnode Hcommi Hreg' Hrdi
  ihave #Hlinv' : srvRaftLogInv E.γr.raft $$ []
  · iunfold rnEnvOk at Henv'
    icases Henv' with ⟨-, -, -, #H, -⟩
    iexact H
  ihave #Hprop : raftPropose E.γr.raft (rnNodeIface γw) $$ []
  · iapply raftPropose_of_isNode E γw (wp_Propose γw.node)
    iframe Hpkg Henv' Hisnode Hlinv'
  ihave #Hfix' : rnFixed a
      { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } $$ []
  · simp only [rnFixed]
    iexact Hfix
  have hn0 : ({ rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } :
      raftNode).raftNodeConfig'.Node' =
      interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.node.ty) #γw.nl.loc := by
    simp only [Hrvcfg, rnNodeIface, Hwnl]
  ihave #Hstate : rnReplayState γw rv.raftNodeConfig'.initialReplayTerms' γw.snap0 $$ []
  · rw [Hrvcfg]
    iunfold rnReplayState
    iexists (σ.ents.map EntryModel.ofM).foldl replayAddEntry []
    isplitr
    · iExactEq Hseed; rfl
    ipureintro
    rw [Hwa0, Hws0]
    exact replaySeed_pending S σ A₀ Hhold hseed.2.1 (hseed.1.imp fun h => h.2) hseed.2.2
  imod (isRaftNode_of_rnParts E γw a
    { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } hn0 Hb30)
    $$ [Htrf Hlts Hreplay Hmu' Hdtok] with ⟨#Hrn, Hdone, #Hnodef, #Htrf⟩
  · iframe Hpkg Henv' Hfits' Hrsb Hreg' Hfix' Htrf Hlts Hreplay Hmu' Hdtok Hstate
    isplitr
    · -- the restart data: the restart disjunct
      iunfold rnRestartOk; iright
      isplitr
      · ipureintro; rw [Hwpre, Hws0, Hwa0, Hwc0]; exact ⟨rfl, Hba, Hac, by rw [Hwnode]; exact Hnsm⟩
      rw [Hsrv, Hwa0]; iexact HA0
    simp only [Hrvcfg]
    iframe Hidri Hsti Htri Hmsi
    isplitr
    · rw [← Hwnl]
      iexact Hni
    isplitr
    · ipureintro; exact Hwms.symm
    isplitr
    · rw [Hwwal, Hwnode]; iexact Hdur
    iunfold rnParts at Hparts
    iunfold rnParts
    iNamed Hparts
    simp only [named]
    iframe #
  imodintro
  iframe Hrn Hdone Htrf Hprop
  have hn : rnNodeIface γw =
      ({ rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } : raftNode).raftNodeConfig'.Node' := by
    simp only [Hrvcfg, rnNodeIface, Hwnl]
  rw [hn]
  iexact Hnodef


end compose

end EtcdGrove
end Perennial
