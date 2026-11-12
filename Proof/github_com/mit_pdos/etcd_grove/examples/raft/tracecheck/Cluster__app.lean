/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Cluster__app.lean`. Lean-first
(no Rocq counterpart).

The loop keeps the node idle with its durable state, view, liveness, the storage's metadata, the
adders' share and a thread token. Each iteration `select`s on the stop channel (the broadcast: return,
the deferred `ticker.Stop()` and `c.apps.Done()` with the liveness and the share), the ticker
(`node.Tick`) and the node's `Ready` channel, received by the traced law (`isReadyChan_recvAu.tracedSpec_proof`:
`readyGotT`, the claim on the `Ready`'s messages). A `Ready`: a snapshot is refuted (`probeA_noSnap`); *enter* runs
with the durable state and the liveness; `handleReady`; `Advance` with the claim
(`node.Advance.tracedSpec`: each message's token, `trTok`; the stopped answer refuted by the liveness); then
each message, its `msgOwn`, `sentMsg`, credits and token (`probeA_msgs`), is cloned
(`proto.ClonePb` at `pbMessage`, the clone owned without responses: `clone_st`) and sent.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__app
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__handleReady
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.below
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Perennial.Proof.time.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 ProbeA

/-- The `Ready`'s batch ends below `2^61` (its last index within the time receipts past the bootstrap
log, `readyRest`'s bound). -/
theorem tc_batch_bound [GooseExts] (es : List EntryM) (Lx : Int) (R b : Nat)
    (h1 : ∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ Lx + 1)
    (h2 : Lx < (R : Int) + b) (h3 : R + b ≤ 2 ^ 61) :
    ∀ e0, es.head? = some e0 → uint.nat e0.Index' + es.length ≤ 2 ^ 61 := by
  intro e0 he
  have := h1 e0 he
  have h4 : ((R + b : Nat) : Int) ≤ 2 ^ 61 := by exact_mod_cast h3
  push_cast at h4
  have h5 : (uint.nat e0.Index' : Int) = uint.Z e0.Index' := by word
  omega

theorem tc_delay_pos (d : w64) (h0 : 0 ≤ sint.Z d) (h1 : sint.Z d < 2 ^ 62) :
    0 < sint.Z (d + W64 1) := by word

theorem tc_range_lt (k len : w64) (n : Nat) (h : sint.Z k < sint.Z len) (h1 : n = sint.nat len)
    (h0 : 0 ≤ sint.Z k) : sint.nat k < n := by
  subst h1; word

theorem tc_range_succ (k len : w64) (h : sint.Z k < sint.Z len) (h0 : 0 ≤ sint.Z k) :
    0 ≤ sint.Z (k + W64 1) ∧ sint.nat (k + W64 1) = sint.nat k + 1 ∧
      sint.Z (k + W64 1) ≤ sint.Z len := by
  refine ⟨by word, by word, by word⟩

theorem tc_toNat_sint' (k : w64) (_h : 0 ≤ sint.Z k) : (sint.Z k).toNat = sint.nat k := by word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [MemStorReg GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

attribute [local instance] memStorageModel

theorem Cluster.app.wp_proof
    (wp_AdvanceT : node.Advance.tracedSpec (GF := GF) (hG := hG))
    (wp_handleReady : Cluster.handleReady.spec (GF := GF) (hG := hG))
    (wp_send : Cluster.send.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG))
    (wp_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_Tick : node.Tick.spec (GF := GF) (hG := hG)) :
    Cluster.app.spec (GF := GF) (hG := hG) := by
  intro _ c W r n ms γs id st v hs0 q Hh Hst Hv
  wp_start as ⟨#Hw, #Hri, Hown, Hmeta, Hdrv, Hrs, Hcfg, Hrun, Hdone, Had, Htt⟩
  ihave #Hw' := Hw
  iunfold tcWorld at Hw'
  icases Hw' with ⟨#HcTick, #HcMax, #HcDrop, #HcSnap, %Hpure, #Hstop, #Hsc, #Hrsro, #Hnodes, #Hnj,
    #Hiso, #HcP, #HcD, #HcX, #HcR, #HcC, #Hclu, #Hops, #Hpol, #Hsn, #Hboot⟩
  ihave #Hri' := Hri
  iunfold repInfo at Hri'
  icases Hri' with ⟨#Hid, #Hnf, #Hsf, #Hnode, #Hreg, #Hlock⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hsy : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply time.wp_NewTicker W.cfg.Tick' as %t %tch %γt #Ht
  · ipureintro; exact Hpure.2.1
  ihave #Ht' := Ht
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨#HtC, #HtI, #HtR, #Htbag⟩
  try wp_auto
  ihave IH : iprop(∃ (st : NodeDriverState) (v : ConfigView) (hs : HardStateM),
      "Hdrv" ∷ nodeDriver n W.cl tcRaftN st ∗ "Hrs" ∷ raftState W.cl id st.durable ∗
      "Hcfg" ∷ nodeConfig n W.cl tcRaftN v ∗ "Hrun" ∷ nodeRunning n W.cl tcRaftN 1 ∗
      "Hown" ∷ repOwn r ∗ "Hmeta" ∷ memStorMeta ms γs hs ∗
      "Had" ∷ njAdder tcNetN (c.[G.Cluster, go!"net"]) W.nj q ∗ "Htt" ∷ threadTok ∗
      "%Hst" ∷ ⌜st.handling = none ∧ st.storage = memStorIface ms ∧ ViewOk st.delivered v⌝)
    $$ [Hdrv Hrs Hcfg Hrun Hown Hmeta Had Htt]
  · iexists st, v, hs0
    iframe
    ipureintro; exact ⟨Hh, Hst, Hv⟩
  wp_for IH
  wp_apply (lc := 2) wp_Ready W.cl tcRaftN id n $$ [$Hraft $Hnode] as %ch #Hch
  try wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the stop channel closed: return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, W.sc, W.γsc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hsc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hsc
    iintro ⟨-, -⟩
    try wp_auto
    wp_for_post
    try wp_auto
    wp_apply time.Ticker.wp_Stop t $$ []
    · iexists tch, γt; iexact Ht
    try wp_auto
    wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done (appDone c W r id q) _)
      $$ [$Hsy $Hdone Hrun Had]
    · unfold appDone; iexists n; iframe Hnf Hnode Hrun Had
    try wp_auto
    iapply HΦ
    iexact Htt
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a tick
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %tm0 -
    wp_auto_lc 2
    wp_apply wp_Tick n W.cl tcRaftN id $$ [$Hraft $Hnode]
    try wp_auto
    wp_for_post
    iframe
    iexists st, v, hs
    iframe
    ipureintro; exact Hst
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a `Ready`
    simp only [chan.blockingClausePre]
    icases isReadyChan_recvAu.tracedSpec_proof n ch W.cl tcRaftN id st _ Hst.1 $$ Hch Hnode Hdrv with ⟨%γc, #Hchan, Hau⟩
    iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hchan
    iapply Hau $$ [$Hlc1 $Hlc2]
    inext
    iintro %rdv Hgot
    iunfold readyGotT at Hgot
    icases Hgot with ⟨%ce, %es, %h, %L, %qs, %ss, #Hce, #Hcomm, -, Hrest, -, Henter, #Hdl, -, Hcl⟩
    iunfold readyRest at Hrest
    icases Hrest with ⟨#Hes, Hmsl, Hmsok, #Hhs, -, %Hbnd, Hsnap, -⟩
    cases L with
    | some l =>
      imod probeA_noSnap W.cl tcRaftN id rdv st ce es l ⊤ (fun _ _ => CoPset.mem_full)
        $$ Hclu Hsn Hsnap with %F
      exact F.elim
    | none =>
    iunfold readySnap at Hsnap
    icases Hsnap with ⟨%Hnull, Happ, -, %Hidx⟩
    iunfold readyEnter at Henter
    imod Henter $$ %⊤ %(1 : Qp) %(by simp) [$Hrs $Hrun] with ⟨Hrs, Hrun, Hdrv, #Hmsgs⟩
    simp only [NodeDriverState.afterReady]
    try wp_auto
    obtain ⟨Lx, -, HL1, -, HL2⟩ := Hbnd
    have Hbound : ∀ e0, es.head? = some e0 →
        (∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j) ∧
        uint.nat e0.Index' + es.length ≤ 2 ^ 61 :=
      fun e0 he => ⟨(Hidx e0 he).1, tc_batch_bound es Lx _ _ HL1 HL2 Hpure.2.2.2.2.2.2 e0 he⟩
    ihave Happ' : appendRight (memStorIface ms) es $$ [Happ]
    · rw [← Hst.2.1]; iexact Happ
    wp_apply wp_handleReady c W r n ms γs id rdv st.delivered ce es h hs v Hst.2.2 Hbound
      $$ [Hown Hmeta Happ' Hcfg Hrun] as ⟨Hown, %hs1, %v1, Hmeta, Hrcpt, Hcfg, Hrun, %Hv1⟩
    · iframe Hw Hri Hce Hcomm Hdl Hes Hhs Hown Hmeta Happ' Hcfg Hrun
      ipureintro; exact Hnull
    try wp_auto
    -- `Advance`, with the claim: the messages' tokens
    ihave Hrcpt' : advReceipt st.storage (st.delivered ++ ce).length es none $$ [Hrcpt]
    · rw [Hst.2.1]; iexact Hrcpt
    have Hsk := skippedIn_noConf (GF := GF) W.cl (st.delivered ++ ce) v1.applied
      (st.delivered ++ ce).length Hv1.2.2
    ihave #Hsk' := Hsk
    wp_apply wp_AdvanceT n W.cl tcRaftN id (st.afterReady ce es h none ss) es none v1 qs rfl
        (fun _ h => by cases h) $$ [Hdrv Hrcpt' Hcfg Hcl] as Hpost
    · iframe Hclu Hnode Hcfg Hcl
      isplitl [Hdrv]
      · iExactEq Hdrv; rfl
      isplitl [Hrcpt']
      · iExactEq Hrcpt'; rfl
      iExactEq Hsk'; rfl
    icases Hpost with (⟨Hdrv, -, Hcfg, Htoks⟩ | ⟨Hstop, -⟩)
    · ihave Hall := probeA_msgs W.cl tcRaftN id qs $$ Hmsok Hmsgs Htoks
      ihave %Hmlen := ownSlice_len $$ Hmsl
      simp only [List.length_map] at Hmlen
      ihave IHm : iprop(∃ (k : w64) (mv : Loc),
          "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗ "Hmsl" ∷ rdv.Messages' ↦* qs.map QMsg.loc ∗
          "Had" ∷ njAdder tcNetN (c.[G.Cluster, go!"net"]) W.nj q ∗ "Htt" ∷ threadTok ∗
          "Hall" ∷ ([∗list] q' ∈ qs.drop (sint.nat k), (msgOwn q'.loc (readyDq q'.st) q'.st ∗
            sentMsg W.cl tcRaftN id q'.st ∗ msgCredits W.cl tcRaftN q'.st) ∗ trTok W.cl q'.st) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rdv.Messages'.len⌝)
        $$ [i m Hmsl Had Htt Hall]
      · iexists W64 0, _
        iframe i m Hmsl Had Htt
        simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
        iframe Hall
        ipureintro; exact ⟨by decide, by have := Hmlen.2; word⟩
      wp_for IHm
      wp_if_destruct
      · have Hlt := tc_range_lt k _ qs.length Hif Hmlen.1 Hk.1
        obtain ⟨qm, Hq⟩ : ∃ qm, qs[sint.nat k]? = some qm := ⟨_, List.getElem?_eq_getElem Hlt⟩
        have Hql : (qs.map QMsg.loc)[sint.nat k]? = some qm.loc := by
          rw [List.getElem?_map, Hq]; rfl
        simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv.Messages'.len from ⟨Hk.1, Hif⟩,
          _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index rdv.Messages' (sint.Z k) _ (DFrac.own 1) qm.loc Hk.1
          $$ [Hmsl] as Hmsl
        · iframe Hmsl; ipureintro; rw [tc_toNat_sint' k Hk.1]; exact Hql
        have Hdrop : qs.drop (sint.nat k) = qm :: qs.drop (sint.nat k + 1) := by
          rw [List.drop_eq_getElem_cons Hlt]
          rw [List.getElem?_eq_getElem Hlt] at Hq
          rw [Option.some.inj Hq]
        rw [Hdrop]
        icases Hall with ⟨⟨⟨Hmo, #Hs, Hcr⟩, Htok⟩, Hall⟩
        obtain ⟨Hs0, Hs1, Hs2⟩ := tc_range_succ k _ Hif Hk.1
        try wp_auto
        -- the clone
        ihave %Hsh := sentMsg_shape W.cl tcRaftN id qm.st $$ Hs
        have hr : qm.st.resps = [] := by
          have := Hsh.1; unfold SentMsgShape at this; exact this.2.2.2.2.2.2.2
        imod msgOwn_persist qm.loc (readyDq qm.st) qm.st $$ Hmo with #Hro
        have Hcln := wp_Clone (pbMessage (GF := GF)) qm.loc qm.st
        simp only [pbMessage_ty, pbMessage_ro] at Hcln
        ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
        · iPkgInit
        wp_apply Hcln $$ [$Hproto $Hro] as %l' ⟨%st', Hdec, %Heqv⟩
        have Hst' := clone_st qm.st st' hr Heqv
        subst Hst'
        wp_apply wp_below (W.cfg.MaxDelay' + W64 1)
          (tc_delay_pos _ Hpure.1.2.2.2.2.1 Hpure.1.2.2.2.2.2.1) $$ [$Hpkg] as %dl -
        try wp_auto
        wp_apply wp_below (W64 100) (by decide) $$ [$Hpkg] as %dp -
        try wp_auto
        ihave #Hrn : repNode W.cl r id $$ []
        · iunfold repNode; iexists n; iframe Hnf Hnode
        wp_apply wp_send c W r id l' qm.st _ _ q $$ [$Hpkg $Hw $Hrn $Hdec $Hs $Hcr $Htok $Had $Htt]
          as ⟨Had, Htt⟩
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, qm.loc
        rw [Hs1]
        iframe
        ipureintro; exact ⟨Hs0, Hs2⟩
      · wp_for_post
        iframe
        iexists _, v1, hs1
        iframe Hdrv
        isplitl [Hrs]
        · iExactEq Hrs; rfl
        iframe Hcfg Hrun Hown Hmeta Had Htt
        ipureintro
        exact ⟨rfl, Hst.2.1, Hv1⟩
    · iexfalso
      iapply nodeRunning_stopped n W.cl tcRaftN 1
      iframe Hrun Hstop
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end TraceCheck
end EtcdGrove
end Perennial
