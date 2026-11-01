/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.StartNode
public import Spec.go_etcd_io.raft.v3.setupNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Proof.go_etcd_io.raft.v3.ApiVocab
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.InvApiJoin
import Proof.go_etcd_io.raft.v3.InvApiBoot
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.SnapValidCert
import Proof.go_etcd_io.raft.v3.StepGhostMode
import Proof.go_etcd_io.raft.v3.InvStorageRead
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import Proof.go_etcd_io.raft.v3.ConfchangeApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

`setupNode` (`NewRawNode`, `Bootstrap`, `newNode`), then as `RestartNode`'s from `newNode` on: the
node's ghost state (the channels' hand-shakes, the tick channel's invariant, `dlv` and `rof`, the
configuration shared with the driver at the peers), `go n.run()` with `runPre` at the delivered log
`[]` (D12: the boot entries reach the application through the first `Ready`s), the term ceiling at
the bootstrap term `1` (the budget's, `budget_alloc_boot`). (2026-10-30, stage R5: restored from
U9's deletion, over `NewRawNode`'s boot bundle.)
-/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the section header. -/
private abbrev StartNode.specRaw : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (sn : StorNames)
    (gdlm gcap gccq gcam glive : GName)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → σ.pend = [] →
  σ.fr = 0 → σ.sg = 0 → σ.dt = ∅ →
  HsEmpty hs →
  csm.Voters' = [] →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  σ.fl = W64 0 →
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  γ.reNoSnap = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 1) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 0) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ ∗ R' }}) ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      bootInit γ md cv.ID' (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      -- the cluster's term budget, at least at the bootstrap term `1` (`budget_alloc_boot`)
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) ∗
      certLink γ sn ∗
      -- the configuration names' initial states
      monoListAuthOwn gdlm 1 ([] : List EntryM) ∗ monoListLbOwn gdlm ([] : List EntryM) ∗
      dghostVar gcap (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet ps) ∅) ∗
      dghostVar gccq (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet ps) ∅) ∗
      monoNatAuthOwn gcam 1 0 ∗ monoNatLbOwn gcam 0 ∗ dghostVar glive (DFrac.own 1) false }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = md ∧ γn.sn = sn ∧
         nd = interface.mkOk (go.GoType.PointerType node.ty) #n ∧
         γn.dlm = gdlm ∧ γn.cap = gcap ∧ γn.ccq = gccq ∧ γn.cam = gcam ∧ γn.live = glive⌝ ∗
        R' ∗
        isNodeChan γn cv.ID' n ∗ nodeDriverChan γn cv.ID' n [] hsZero ∗
        nodeLiveRaw γn 1 ∗
        nodeCfg γn 0 (cfgState (GMap.listToSet ps) ∅) ∗
        peers ↦*{dq} pv }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem StartNode.wp_raw
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.specRaw (GF := GF) (hG := hG) := by
  intro γ md bud c cv lok si sn γdlm γcap γccq γcam γlive σ hs csm R R' peers dq pv ps ctxs bootLog
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 S1 S2 S3 S4 S5 S6 Hhs Q1 Q2 Q3 Q4 Q5 Hfl0
    R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
  wp_start as ⟨Hc, #Hlg, HR, #HFI, #HLI, #HIS, Hpeers, #Hctx, #Hmarshal, Hghost, #Hcommitted,
    #Hbud, #Hlb0, #Hcl, Hdlm, #Hdlb, Hcap, Hccq, Hcam, #Hcamlb, Hlive⟩
  ihave #Hcinv : raftCommitInv γ $$ [Hghost]
  · iapply bootInit_inv γ md cv.ID' _ bootLog $$ Hghost
  wp_auto
  wp_apply wp_setupNode γ md c cv lok si sn σ hs csm R R' peers dq pv ps ctxs bootLog
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 S1 S2 S3 S4 S5 S6 Hhs Q1 Q2 Q3 Q4 Q5 Hfl0
    R1 R2 R3 R4 R5 R6 R7 R8 R9 R10
    $$ [$Hc $Hlg $HR $HFI $HLI $HIS $Hpeers $Hctx $Hmarshal $Hghost $Hcommitted $Hcl]
    as %np ⟨HR', %nv, %rn, Hnp, %Hnvrn, Hchans, Hrn, Hpeers⟩
  ipersist Hnp
  try wp_auto
  ipersist n
  -- the node's ghost state
  imod dghostVar_alloc ((([] : List EntryM), hsZero) : List EntryM × HardStateM) with ⟨%γdlv, Hdlv⟩
  icases dghostVar_halves _ _ $$ Hdlv with ⟨Hdlv1, Hdlv2⟩
  imod dghostVar_alloc (([], [], [], hsZero, none) : List EntryM × List EntryM ×
    List EntryM × HardStateM × Option SnapLoan) with ⟨%γrof, Hrof⟩
  icases dghostVar_halves _ _ $$ Hrof with ⟨Hrof1, Hrof2⟩
  -- (2026-10-15, stage N) the configuration shared with the driver
  icases dghostVar_halves _ _ $$ Hcap with ⟨Hcap1, Hcap2⟩
  icases dghostVar_halves _ _ $$ Hccq with ⟨Hccq1, Hccq2⟩
  -- (D19i part 1) the driver's request on `advancec`
  imod dghostVar_alloc (((none, none) : AdvReq)) with ⟨%γreq, Hreq⟩
  icases dghostVar_halves _ _ $$ Hreq with ⟨Hreq1, Hreq2⟩
  -- (2026-10-29, stage U9a) whether the node is stopped: the client's half and `run`'s
  icases dghostVar_halves _ _ $$ Hlive with ⟨Hlive1, Hlive2⟩
  unfold newNodeChans
  icases Hchans with ⟨%γp, %γr, %γc, %γcs, %γrd, %γa, %γt, %γd, %γs, %γst, #Hcp, Hop, #Hcr, Hor,
    #Hcc, Hoc, #Hccs, Hocs, #Hcrd, Hord, #Hca, Hoa, #Hct, Hot, #Hcd, Hod, #Hcs, Hos, #Hcst, Host⟩
  let γn : NodeNames := { raft := γ, id := cv.ID', bud := bud, stor := interface.ok si, propc := γp,
                          recvc := γr, confc := γc, confstatec := γcs, readyc := γrd, advancec := γa, tick := γt,
                          done := γd, stop := γs, status := γst, dlv := γdlv, rof := γrof,
                          mode := md, dlm := γdlm, cap := γcap, ccq := γccq, cam := γcam, req := γreq,
                          sn := sn, live := γlive }
  ihave Hlive1 : nodeLiveRaw (GF := GF) γn 1 $$ [Hlive1]
  · unfold nodeLiveRaw; iexact Hlive1
  ihave Hlive2 : nodeLiveRaw (GF := GF) γn 1 $$ [Hlive2]
  · unfold nodeLiveRaw; iexact Hlive2
  imod start_handshake nv.propc' (propP γn) iprop(True) γp $$ Hcp Hop with #Hhp
  imod start_handshake nv.recvc' (netP γn cv.ID') iprop(True) γr $$ Hcr Hor with #Hhr
  imod start_handshake nv.confc' (confcP γn) iprop(True) γc $$ Hcc Hoc with #Hhc
  imod start_handshake nv.confstatec' (confstateP γn) iprop(True) γcs $$ Hccs Hocs with #Hhcs
  imod start_handshake nv.readyc' (readyP γn) iprop(True) γrd $$ Hcrd Hord with #Hhrd
  imod adv_start γn nv.rn' cv.ID' nv.advancec' $$ Hca Hoa with #Hha
  imod alloc_broadcast_chan (nodeStoppedRaw γn) γd nv.done' $$ Hcd Hod with Hpend
  icases ownBroadcastChan_pending_unknown nv.done' γd (nodeStoppedRaw γn) $$ Hpend with ⟨Hpend, #Hhd⟩
  imod start_handshake nv.stop' (fun (_ : Unit) => nodeLiveRaw γn 1) iprop(True) γs $$ Hcs Hos
    with #Hhs
  imod start_handshake nv.status' statusChP iprop(True) γst
    $$ Hcst Host with #Hhst
  imod tickCred_zero bud with Hcr0
  imod inv_alloc tickN ⊤ (tickInv γn) $$ [Hot Hcr0] with #Htickinv
  · inext
    unfold tickInv
    iexists []
    iframe
  icases ownRawNode_shared γ rn cv.ID' _ $$ Hrn with ⟨%r, %lok', #Hrr, #Hrid, #Hrlg, #Hlg', Hrn⟩
  ihave #Hnode : isNodeChan γn cv.ID' np $$ []
  · unfold isNodeChan
    iexists nv, r, lok'
    simp only [named]
    rw [Hnvrn]
    iframe #
    ipureintro; rfl
  -- `go n.run()`
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1]
  · wp_apply wp_node_run γn cv.ID' np $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], [], hsZero, none) : List EntryM × List EntryM × List EntryM ×
        HardStateM × Option SnapLoan)
      rw [Hnvrn]
      iframe Hnp Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hdlv1 Hlb0
      iframe Hpend Hlive1
      unfold runCfg
      isplitr
      · ipureintro
        exact ⟨rfl, Nat.le_refl _, rfl, fun _ h => by simp at h, rfl⟩
      isplitl [Hdlm]
      · iExactEq Hdlm; rfl
      isplitr
      · simp only [rsDlv]
        iapply dlvKeysAt_nil
      iexists 0
      iframe Hcap1 Hcam
      isplitr
      · ipureintro; exact Nat.le_refl _
      iapply undecFree_empty
    itrivial
  iapply HΦ
  iexists γn, np
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  iframe Hnode Hlive2 HR' Hpeers
  isplitl [Hdlv2 Hreq1 Hreq2]
  · unfold nodeDriverChan dlvLb
    iframe Hnode Hdlv2 Hdlb
    isplitr
    · iapply dlvKeysAt_nil
    iexists _
    iframe Hreq1 Hreq2
  unfold nodeCfg
  iframe Hcap2 Hcamlb
  iexists _
  iframe Hccq1 Hccq2


end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Raft's log namespace is in the cluster's. -/
private theorem raftLogN_sub (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (HNs : γ.raft.reNs = N .@ "raft") : (↑(raftLogN γ.raft) : CoPset) ⊆ E := by
  intro p hp
  unfold raftLogN raftN at hp; rw [HNs] at hp
  exact HE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p hp))

/-- **A valid snapshot's certificates** (the API's `snapshotValid` read back at raft's level). -/
private theorem snapValid_raftCert (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (_HU : UniNames γ N) (sv : SnapshotM) :
    ⊢ clusterInv (GF := GF) γ N -∗ EtcdGrove.snapshotValid (GF := GF) γ sv ={E}=∗
      raftSnapCertD γ.raft (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  iintro #Hci Hv
  unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
  icases Hv with ⟨%l, %m, #Hlb, #Ha, #Hm, %Hp⟩
  obtain ⟨Hlen, -, Hlast, Hcs, H61, Hsz⟩ := Hp
  ihave %Hval := confAt_valid_impl γ l.length m $$ Ha
  ihave %Hres := confAtU_restorable γ l.length m $$ Ha
  iunfold confAtU at Ha
  icases Ha with ⟨%l2, %M, #Hlb2, #HM, %P2⟩
  obtain ⟨hk, c0, g, hm, hf⟩ := P2
  icases isCommittedLogLb_agree_impl γ l l2 $$ [Hlb Hlb2] with %Hcm
  · iframe Hlb Hlb2
  have Hfold : decFold M c0 l = some m := by
    rw [← List.take_length (l := l), take_eq_of_cmp l l2 l.length Hcm (Nat.le_refl _) hk]
    exact hf
  iunfold snapMadeU at Hm
  icases Hm with ⟨%gr, %K, %key, %Hk, #HK, -⟩
  obtain ⟨Hreg, HkK, Hmat⟩ := Hk
  have hm' := hm
  obtain ⟨⟨h0, -, hd, -, Hsok, -, -⟩, -⟩ := hm'
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  imod api_lb_committed γ N E HE l $$ Hci Hlb with ⟨%L, %HL, #HLc⟩
  have HD : (DynCfg.ofFold noDec (stOf c0) h0).fold M L = some (cfgOf m) := by
    rw [hm.fold _ hd M L, HL, Hfold]; rfl
  have HLlen : L.length = uint.nat sv.Metadata'.Index' := by rw [← Hlen, ← HL, strip_length]
  have HLlast : L.getLast?.map EntryM.Term' = some sv.Metadata'.Term' := by
    rw [← Hlast, ← HL]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl
  obtain ⟨hcv, hco, hcl, hcn, hal⟩ := Hcs
  unfold EtcdGrove.Membership.Valid memValid at Hval
  obtain ⟨Hz, Hni⟩ := Hres
  iapply raftSnapCertD_snapTrip γ.raft E L sv (cfgOf m) _ M gr K key
    (raftLogN_sub γ N E HE HNs) hd Hreg Hsok HLlen (by rw [HLlen, ← Hlen]; exact H61) HLlast
    hcv hco hcl hcn hal Hval.1
    (fun x hx h0x => Hz (by
      subst h0x
      simp only [Membership.ids, GMap.elem_of_union]
      rcases hx with h | h | h | h
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h))
    (fun x hx => Hni x hx) Hsz HD HkK (by rw [HLlen, ← Hlen]; exact Hmat.1) Hmat.2
    $$ Hcinv HLc HM HK

/-- Raft's reading of the contract's `Bnd`: an applied lower bound or a snapshot handed out of the
node's storage names (its table's entry). -/
private theorem storBnd_raftBnd (γ : Cluster) (id : w64) (sn : StorNames) (c : Nat) :
    ⊢ nodeStorNames (GF := GF) γ id sn -∗ monoNatLbOwn sn.ga 0 -∗ EtcdGrove.storBnd γ id c -∗
      raftBnd sn c := by
  iintro #Hsn #H0 Hb
  unfold EtcdGrove.storBnd EtcdGrove.nodeAppliedLb EtcdGrove.snapGiven nodeAppliedLbU snapGivenU
    raftBnd
  icases Hb with ⟨%k, %Hk, ((%Hk0 | ⟨%sn', #Hsn', (#Hl | #Hl)⟩) | ⟨%sn', #Hsn', #Hl⟩)⟩
  · iexists 0
    isplitr; · ipureintro; omega
    ileft; iexact H0
  · ihave %He := nodeStorNames_agree γ id sn' sn $$ Hsn' Hsn
    subst He
    iexists k
    isplitr; · ipureintro; exact Hk
    ileft; iexact Hl
  · ihave %He := nodeStorNames_agree γ id sn' sn $$ Hsn' Hsn
    subst He
    iexists k
    isplitr; · ipureintro; exact Hk
    iright; iexact Hl
  · ihave %He := nodeStorNames_agree γ id sn' sn $$ Hsn' Hsn
    subst He
    iexists k
    isplitr; · ipureintro; exact Hk
    iright; iexact Hl

/-- Raft's reading of the contract's `DL` for a valid snapshot: the node's delivered committed log
reaches its index, so raft certified the term there (`dlvKeys`, of the node's storage names). -/
private theorem storDL_raftDL (γ : Cluster) (id : w64) (sn : StorNames) (sv : SnapshotM)
    (Hdyn : ∀ γn : NodeNames, NodeOk γ γn → γn.mode.isDyn = true) :
    ⊢ nodeStorNames (GF := GF) γ id sn -∗ EtcdGrove.snapshotValid γ sv -∗
      EtcdGrove.storDL γ id (uint.nat sv.Metadata'.Index') -∗
      raftDL sn (uint.nat sv.Metadata'.Index') sv.Metadata'.Term' := by
  iintro #Hsn Hv Hdl
  unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.storDL EtcdGrove.isNode
    EtcdGrove.deliveredLogLb
  icases Hv with ⟨%l1, %m, #Hlb1, -, -, %Hp⟩
  obtain ⟨Hlen, Hpos, Hlast, -⟩ := Hp
  icases Hdl with ⟨%n, %N', %l, Hnode, Hdlv, %Hi⟩
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn0, -, #Hch0, -⟩
  iunfold deliveredLogLb at Hdlv
  icases Hdlv with ⟨⟨%γn, %id', %ds, %Hf, #Hch, (%Hnd | #Htab), #Hdk⟩, #Hlb⟩
  · exfalso; rw [Hdyn γn Hf.1] at Hnd; cases Hnd
  ihave %Hid := isNode_id_agree γn0 γn id id' n $$ Hch0 Hch
  subst Hid
  ihave #Hsn2 := nodeTabOk_storNames γ id γn $$ Htab
  ihave %Hs := nodeStorNames_agree γ id γn.sn sn $$ Hsn2 Hsn
  icases isCommittedLogLb_agree_impl γ l1 l $$ [Hlb1 Hlb] with %Hcm
  · iframe Hlb1 Hlb
  have Hpre : l1 <+: l := by
    rcases Hcm with h | h
    · exact h
    · have e := h.eq_of_length (by have := h.length_le; omega)
      rw [e]
      exact ⟨[], List.append_nil _⟩
  obtain ⟨t, Ht⟩ := Hpre
  have Hj : l1.length - 1 < l1.length := by omega
  have Hl1j : l1[l1.length - 1]?.map LogEntry.term = some sv.Metadata'.Term' := by
    rw [← List.getLast?_eq_getElem?]; exact Hlast
  have Hlj : l[l1.length - 1]? = l1[l1.length - 1]? := by
    rw [← Ht, List.getElem?_append_left Hj]
  rw [← Hlj, ← Hf.2] at Hl1j
  unfold strip at Hl1j
  rw [List.getElem?_map, Option.map_map] at Hl1j
  cases hde : ds[l1.length - 1]? with
  | none => rw [hde] at Hl1j; cases Hl1j
  | some e =>
    rw [hde] at Hl1j
    simp only [Option.map_some, Option.some.injEq, Function.comp] at Hl1j
    iunfold dlvLb at Hdk
    icases Hdk with ⟨-, #Hk⟩
    iunfold dlvKeys at Hk
    iunfold dlvKeysAt at Hk
    ihave #Hke := (BigSepL.bigSepL_lookup (Φ := fun j (e : EntryM) =>
      iprop((0 + j + 1) ↪[γn.sn.gd]□ e.Term' : IProp GF)) hde) $$ Hk
    unfold raftDL
    ileft
    rw [← Hs, show uint.nat sv.Metadata'.Index' = 0 + (l1.length - 1) + 1 by omega, ← Hl1j]
    iExactEq Hke; rfl

/-- **The certificate link of fresh storage names** (`certLink`): their `SV` pin the API's
`snapshotValid`, their snapshot pin raft's certificate. -/
private theorem certLink_make (γ : Cluster) (N : Namespace) (HU : UniNames γ N) (sn : StorNames) :
    ⊢ clusterInv (GF := GF) γ N -∗
      savedPredOwn sn.gsv DFrac.discard (EtcdGrove.snapshotValid (GF := GF) γ) -∗
      savedPredOwn sn.gk DFrac.discard (raftSnapCertD (GF := GF) γ.raft) -∗ certLink γ.raft sn := by
  iintro #Hci #Hsv #Hgk
  have HcN : raftCertN γ.raft = N := HU.2.2.1
  unfold certLink storCertOk
  isplitr
  · iintro !> %sv %E %HE Hc
    rw [HcN] at HE
    unfold svCert
    icases Hc with ⟨%SV, #Hp, #HSV⟩
    ihave #Heq := saved_pred_agree sn.gsv DFrac.discard DFrac.discard SV
      (EtcdGrove.snapshotValid (GF := GF) γ) sv $$ Hp Hsv
    ihave Hv : ▷ EtcdGrove.snapshotValid (GF := GF) γ sv $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HSV
    have : Timeless (EtcdGrove.snapshotValid (GF := GF) γ sv) := by
      have : ∀ s, Timeless (snapMadeU (GF := GF) γ s) := fun s => by
        unfold snapMadeU; infer_instance
      have : ∀ l, Timeless (isCommittedLogLb (GF := GF) γ l) := fun l => by
        unfold isCommittedLogLb; infer_instance
      unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
      infer_instance
    icases Hv with >Hv
    iapply snapValid_raftCert γ N E HE HU sv $$ Hci Hv
  isplitr
  · iintro !> %k %E %HE Hc
    unfold ksnCert
    icases Hc with ⟨%P, #Hp, #HP⟩
    ihave #Heq := saved_pred_agree sn.gk DFrac.discard DFrac.discard P
      (raftSnapCertD (GF := GF) γ.raft) k $$ Hp Hgk
    ihave Hv : ▷ raftSnapCertD (GF := GF) γ.raft k $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HP
    icases Hv with >#Hv
    imodintro; iexact Hv
  · iintro !> %k %E %HE #Hc
    unfold ksnCert
    imodintro
    iexists raftSnapCertD γ.raft
    iframe Hgk
    imodintro; iexact Hc

/-- `StartNode.spec` from the raw triple (2026-10-30, stage R5): the node in the cluster's dynamic
mode of the client's decisions, taking `MsgSnap`s, its ghost state the dynamic one at the bootstrap
state (`rboot`, configuration index `0`), its table entry inserted (`nodeTabOk`), its view at the
voters' membership. -/
private theorem wp_StartNode_impl
    (hS : EtcdGrove.StartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.StartNode.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.StartNode.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.nodeDriver
    EtcdGrove.nodeBoot EtcdGrove.bootStorage EtcdGrove.nodeConfig EtcdGrove.nodeRunning
  intro γ N vs ctxs c cv lok si hs csm Q peers dq pv H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hhs Hv Hvo Hl
    Hln Hal Hps
  iintro %Φ ⟨#Hinit, Hc, #Hlog, Hboot, Hpeers, #Hpc, Htok⟩ HΦ
  iunfold nodeBootU at Htok
  icases Htok with ⟨#Hcl, %Hpf, #Hm, #Hc0, #Hbinv, #Htlb, Hg, ⟨%g, %Hg0, Ha⟩⟩
  obtain ⟨Hid, Hnd, Hnz, Hlen, Hcfg, ⟨gd, Hmr⟩, Hok⟩ := Hpf
  have Hne : vs ≠ [] := fun h => by rw [h] at Hid; exact List.not_mem_nil Hid
  ihave #Hcl' := Hcl
  iunfold isClusterU at Hcl'
  icases Hcl' with ⟨%HU, #Hci, #Hpool⟩
  have Hsl := HU.2.1
  have Hdyn := Hmr.1.2.2.1
  have Hns : γ.raft.reNoSnap = false := Hmr.1.2.2.2.1
  obtain ⟨h0, h1, Hmd⟩ := Hmr.mode
  have HdynOk : ∀ γn : NodeNames, NodeOk γ γn → γn.mode.isDyn = true := fun γn h => by
    rw [h.2.2.2, Hmd]; rfl
  -- the boot bundle
  icases Hboot with ⟨%i, %Rb, %Hi, HRb, #HFI, #HLI, #HIS⟩
  cases Hi
  -- the node's configuration names (`run`'s and the driver's), allocated here so that its table
  -- entry exists before the storage's contract is read
  imod mono_list_own_alloc (GF := GF) ([] : List EntryM) with ⟨%gdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc (GF := GF) ((0 : Nat), cfgState (GMap.listToSet vs) ∅)
    with ⟨%gcap, Hcap⟩
  imod dghostVar_alloc (GF := GF) ((0 : Nat), cfgState (GMap.listToSet vs) ∅)
    with ⟨%gccq, Hccq⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gcam, Hcam, #Hcamlb⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%glive, Hlive⟩
  -- raft's storage names: the applied floor, the snapshot handed out, the certified terms, the
  -- contract's `SV` and the received snapshots' certificate
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%ga, Hga, #Hga0⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gg, Hgg, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := w64) with ⟨%gdd, Hgd⟩
  imod saved_pred_alloc (EtcdGrove.snapshotValid (GF := GF) γ) DFrac.discard trivial
    with ⟨%gsv, #Hsv⟩
  imod saved_pred_alloc (raftSnapCertD (GF := GF) γ.raft) DFrac.discard trivial with ⟨%gk, #Hgk⟩
  let sn : StorNames := ⟨ga, gg, gsv, gdd, gk⟩
  -- the node's table entry
  imod ghost_map_insert_persist cv.ID'
    ((gdlm, gcap, gccq, gcam, glive, ga, gg, gsv, gdd, gk) : CfgNames) (GMap.lookup_empty _)
    $$ Ha with ⟨-, #He⟩
  ihave #Hsn : nodeStorNames (GF := GF) γ cv.ID' sn $$ []
  · unfold nodeStorNames
    iexists g, ((gdlm, gcap, gccq, gcam, glive, ga, gg, gsv, gdd, gk) : CfgNames)
    iframe He
    ipureintro; exact ⟨Hg0, rfl⟩
  ihave #Hlink := certLink_make γ N HU sn $$ Hci Hsv Hgk
  iapply wp_fupd
  iapply (hS γ.raft (γ.mode inferInstance) γ.bud c cv lok si sn gdlm gcap gccq gcam glive
    ({ prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] } : StorState) hs csm
    iprop(Rb ∗ storAuths sn ({ prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] } :
      StorState)) Q peers dq pv vs ctxs γ.raft.reBoot
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 rfl rfl rfl rfl rfl rfl Hhs Hv Hvo Hl Hln Hal rfl Hps Hne Hnd Hnz
    (by omega) Hid Hcfg rfl Hok Hns)
    $$ [Hc HRb Hga Hgg Hgd Hg Hdlm Hcap Hccq Hcam Hlive Hpeers]
  · iframe Hinit Hc Hlog Hc0 Hbinv Htlb Hlink Hdlm Hdlb Hcap Hccq Hcam Hcamlb Hlive Hpeers Hpc Hm
    isplitl [HRb Hga Hgg Hgd]
    · iframe HRb
      unfold storAuths
      isplitl [Hga]
      · iExactEq Hga; rfl
      iframe Hgg
      iExactEq Hgd; rfl
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HFI $$ HRb [HA HΦ']
      inext
      iintro HRb
      iapply HΦ'
      iframe HRb HA
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HLI $$ HRb [HA HΦ']
      inext
      iintro HRb
      iapply HΦ'
      iframe HRb HA
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HIS $$ HRb [HA HΦ']
      inext
      iintro %hp %cs %al ⟨Hhs, Hcs, Hup⟩
      iapply HΦ'
      iframe Hhs Hcs
      imod Hup with ⟨Hst, ⟨%e0, %He0, #Hl0, Hend⟩, HQ⟩
      imodintro
      iframe HQ
      isplitl [Hst]
      · iapply isStorage_of_V
        unfold isStorageV
        iexists EtcdGrove.snapshotValid (GF := GF) γ, EtcdGrove.storBnd (GF := GF) γ cv.ID',
          EtcdGrove.storDL (GF := GF) γ cv.ID'
        isplitl [Hst]
        · iunfold EtcdGrove.isStorage at Hst
          iexact Hst
        isplitr; · iexact Hsv
        isplitr
        · unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt
            EtcdGrove.snapMade
          iintro !> %sv #H
          imodintro; iexact H
        isplitr
        · iintro !> %c' Hb
          iapply storBnd_raftBnd γ cv.ID' sn c' $$ Hsn Hga0 Hb
        · iintro !> %sv Hv Hd
          imodintro
          iapply storDL_raftDL γ cv.ID' sn sv HdynOk $$ Hsn Hv Hd
      unfold ownStorage
      iexists e0
      isplitr
      · ihave H := StorageModel.storCompacted_zero (GF := GF) (interface.ok si)
        iExactEq H; rfl
      isplitr
      · iExactEq Hl0; rfl
      isplitr
      · ihave Hn := StorageModel.storLog_nil (GF := GF) (interface.ok si) 1 (DFrac.own 1)
        iExactEq Hn; rfl
      isplitl [Hend]
      · iright; iExactEq Hend; rfl
      iframe HA
      ipureintro
      exact ⟨He0, Nat.le_refl _, by simp [StorState.kOut], by simp [StorState.kOut], Nat.le_refl _⟩
    · rw [Hmd]
      unfold bootInit
      isplitr
      · ipureintro; exact ⟨Hdyn, stOf_simple _⟩
      -- the dynamic ghost state at the bootstrap state (`raft_dyn_alloc_boot`'s)
      have Hlen' : (γ.raft.reBoot.length : Int) < 2 ^ 64 := by have := Hok.2.1; omega
      unfold ownRaftGhostR
      rw [show (rboot (stOf (Membership.simple (GMap.listToSet vs))) γ.raft.reBoot).p =
        bootPState γ.raft.reBoot from rfl]
      iframe Hg
      isplitr; · ipureintro; exact RInv_rboot _ _ _ Hlen'
      isplitr
      · unfold logRecs rboot
        iapply (BigSepL.bigSepL_nil).2; iempintro
      iintro %h
      exfalso; exact absurd h (by simp [bootPState, initPState])
  iintro !> %nd ⟨%γn, %n, %Hf, HQ, #Hnode, Hdrv, Hlive, Hcf, Hpeers⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd', Hsn', Hnd', Hd1, Hd2, Hd3, Hd4, Hd5⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsl, Hmd'⟩
  have Hdy : γn.mode.isDyn = true := HdynOk γn Hnok
  ihave #Htb : nodeTabOk (GF := GF) γ cv.ID' γn $$ []
  · unfold nodeTabOk
    iexists g
    isplitr; · ipureintro; exact Hg0
    have Hx : cfgNamesOf γn = ((gdlm, gcap, gccq, gcam, glive, ga, gg, gsv, gdd, gk) : CfgNames) := by
      simp only [cfgNamesOf, Hd1, Hd2, Hd3, Hd4, Hd5, Hsn', sn]
    rw [Hx]
    iexact He
  imodintro
  iapply HΦ
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    isplitr; · ipureintro; exact Hnok
    iframe Hnode Htb Hci Hpool
    ipureintro; exact HU
  isplitl [Hdrv]
  · unfold nodeDriver NodeDriverState.init
    iexists γn, cv.ID', []
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
    isplitr; · iexact Hci
    isplitr; · iapply isCommittedLogLb_nil_impl
    isplitr; · ipureintro; exact Hdy
    isplitr; · iexact Htb
    isplitr
    · unfold hsCommitted; ileft; ipureintro; rfl
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  isplitl [Hcf]
  · isplitl [Hcf]
    · unfold nodeConfig
      iexists γn, cv.ID'
      iframe Hnode Htb
      isplitr
      · ipureintro
        refine ⟨Hnok, Hdy, ?_⟩
        show CCGood (stOf (Membership.simple (GMap.listToSet vs)))
        rw [stOf_simple]; exact ccGood_cfgState _
      rw [stOf_simple]; iexact Hcf
    -- (2026-10-30, stage R3) the initial membership, of no entry
    unfold confAtU
    iexists [], ∅
    isplitr; · iapply isCommittedLogLb_nil_impl
    isplitr; · iapply decLb_empty
    ipureintro
    exact ⟨Nat.le_refl _, _, gd, Hmr, rfl⟩
  isplitl [Hlive]
  · -- (2026-10-29, stage U9a) the node runs
    unfold nodeRunning
    iexists γn, cv.ID'
    iframe Hnode Htb Hlive
    ipureintro; exact ⟨Hnok, Hdy⟩
  iframe HQ Hpeers

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem StartNode.wp_proof
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) :=
  ApiImpl.wp_StartNode_impl (StartNode.wp_raw wp_setupNode wp_node_run)

end proof

end EtcdGrove
end Perennial
