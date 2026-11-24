/-
The proof of `KvNet/Spec/.../kvnet/udpTransport__runPeer.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__runPeer
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.fragments
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putMsg
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__nextSeq
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__dropped
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__sendSnapshot
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__writeAll
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpSendLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- **The fragments of a recorded message are datagrams of the protocol**: with the body recorded
under the message's name and its fact, `fragments`' slices, made read-only, are `udpDgsOk`
(`fragsOf_ok`). -/
private theorem frags_dgsOk (F : KvFacts GF) (γu : UdpNames) (src dst boot seq : w64)
    (body : List w8) (dsl : List GoSlice) :
    ⊢ udpMsgAt γu (src, boot, seq) body -∗ udpBodyOk F body -∗
      ([∗list] i ↦ d ∈ dsl, ∃ x, ⌜(fragsOf src dst boot seq body)[i]? = some x⌝ ∗ d ↦* x) ={⊤}=∗
      udpDgsOk F γu dsl := by
  iintro #Hm #Hb Hl
  unfold udpDgsOk
  iapply BigSepL2.bigSepL_fupd
  iapply BigSepL.bigSepL_impl $$ Hl
  imodintro
  iintro %k %d %hk ⟨%x, %hx, Hd⟩
  imod ownSlice_persist d _ x $$ Hd with #Hd
  imodintro
  iexists x
  iframe Hd
  obtain ⟨-, dg, hp, hkey, -, hfrag⟩ := fragsOf_ok src dst boot seq body x (List.mem_of_getElem? hx)
  unfold udpDgOk
  iexists dg
  isplitr
  · ipureintro; exact hp
  unfold udpDgMOk
  iright
  isplitr
  · ipureintro; exact hfrag.1
  unfold udpFragOk
  iexists body
  rw [hkey]
  iframe Hm Hb
  ipureintro; exact hfrag

theorem udpTransport.runPeer.wp_proof
    (wp_nextSeq : udpNet.nextSeq.spec (GF := GF) (hG := hG))
    (wp_fragments : fragments.spec (GF := GF) (hG := hG))
    (wp_putMsg : putMsg.spec (GF := GF) (hG := hG))
    (wp_dropped : udpTransport.dropped.spec (GF := GF) (hG := hG))
    (wp_writeAll : udpTransport.writeAll.spec (GF := GF) (hG := hG))
    (wp_sendSnapshot : udpTransport.sendSnapshot.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)) :
    udpTransport.runPeer.spec (GF := GF) (hG := hG) := by
  intro F γu t γ N id n p pid
  wp_start as ⟨#Ht, #Hp⟩
  ihave #Ht' := Ht
  iunfold isUdpCore at Ht'
  icases Ht' with ⟨%sc, %γsc, #Hb, #Hnode, #Hn, %Htr⟩
  ihave #Hb0 := Hb
  iunfold isUdpBase at Hb
  icases Hb with ⟨%u, %boot, %sp, #Hu, #Hun, #Hstats, #Hs, #Hstopc, #HstopB, -⟩
  ihave #Hun' := Hun
  iunfold isUdpNet at Hun'
  icases Hun' with ⟨%c, %s, %a, %am, %A, #Hid, #Hc, #Hconn, #Ha, #Ham, #HA, #Haddrs, #Hboot, #Hinv,
    #Hmu⟩
  iunfold isUdpPeer at Hp
  icases Hp with ⟨#Hpid, %ch, %γq, #Hch, #Hbag⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto_lc 2
  ihave IH : iprop("Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1) $$ [Hlc1 Hlc2]
  · iframe Hlc1 Hlc2
  wp_for IH
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a message from the queue
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γq
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %mq Hq
    wp_auto_lc 2
    iunfold qElem at Hq
    icases Hq with ⟨%dq, %dqe, %cap, %st, %src, Hm, #Hok, %HTo⟩
    try wp_auto
    wp_apply wp_nextSeq F γu u id boot $$ [$Hpkg $Hun] as %seq %ok Hseq
    try wp_auto
    icases Hseq with (%Hok0 | ⟨%Hok1, Htok⟩)
    · -- no sequence number left: dropped
      subst Hok0
      try wp_auto
      wp_apply wp_dropped F γu t γ N id n mq dq dqe cap st $$ [$Hpkg $Ht $Hm] as Hm
      try wp_auto
      wp_for_post
      iframe HΦ t p
      isplitl [Hlc1]
      · iexact Hlc1
      · iexact Hlc2
    subst Hok1
    try wp_auto
    ihave Hns := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
    ihave Hnc := ownSliceCap_nil (V := w8) (GF := GF)
    wp_apply wp_putMsg slice.nil [] mq dq dqe cap st $$ [$Hpkg $Hns $Hnc $Hm] as %s1 ⟨Hs1, -, Hm⟩
    rw [List.nil_append]
    ihave %Hs1l := ownSlice_len $$ Hs1
    have Hlen : (encMsg st).length < 2 ^ 63 := by have := Hs1l.1; have := Hs1l.2; word
    wp_apply wp_fragments id pid boot seq s1 (DFrac.own 1) (encMsg st) Hlen $$ [$Hpkg $Hs1]
      as %dsv ⟨Hs1, %Hnil, %dsl, Hdsv, %Hdsl, Hel⟩
    imod udp_record γu (id, boot, seq) (encMsg st) ⊤ (by simp) $$ Hinv Htok with #Hmsg
    ihave #Hbody : udpBodyOk F (encMsg st) $$ []
    · iunfold udpBodyOk
      iexists src, st
      iframe Hok
      ipureintro; exact ⟨rfl, Hlen⟩
    imod frags_dgsOk F γu id pid boot seq (encMsg st) dsl $$ Hmsg Hbody Hel with #Hdgs
    imod ownSlice_persist dsv _ dsl $$ Hdsv with #Hdsv
    try wp_auto
    wp_if_destruct
    · -- too long: dropped
      wp_apply wp_dropped F γu t γ N id n mq dq dqe cap st $$ [$Hpkg $Ht $Hm] as Hm
      try wp_auto
      wp_for_post
      iframe HΦ t p
      isplitl [Hlc1]
      · iexact Hlc1
      · iexact Hlc2
    wp_apply wp_GetType.1 mq _ _ _ _ $$ [$Hpb $Hm] as Hm
    try wp_auto
    wp_if_destruct
    · -- a snapshot: its own sender
      wp_apply wp_add sp (W64 2) (by decide) (by decide) $$ [$Hpkg $Hs]
      try wp_auto
      wp_apply wp_fork
      · wp_apply wp_sendSnapshot F γu t γ N id n pid seq dsv dsl $$ [$Hpkg $Ht $Hdsv $Hdgs]
        itrivial
      try wp_auto
      wp_for_post
      iframe HΦ t p
      isplitl [Hlc1]
      · iexact Hlc1
      · iexact Hlc2
    wp_apply wp_writeAll F γu t id sc γsc pid dsv DFrac.discard dsl $$ [$Hpkg $Hb0 $Hdsv $Hdgs]
      as %okw -
    try wp_auto
    cases okw
    · try wp_auto
      wp_apply wp_dropped F γu t γ N id n mq dq dqe cap st $$ [$Hpkg $Ht $Hm] as Hm
      try wp_auto
      wp_for_post
      iframe HΦ t p
      isplitl [Hlc1]
      · iexact Hlc1
      · iexact Hlc2
    · try wp_auto
      wp_apply wp_add sp (W64 17) (by decide) (by decide) $$ [$Hpkg $Hs]
      try wp_auto
      wp_for_post
      iframe HΦ t p
      isplitl [Hlc1]
      · iexact Hlc1
      · iexact Hlc2
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed: return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γsc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
