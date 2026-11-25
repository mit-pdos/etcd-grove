/-
The proof of `KvNet/Spec/.../kvnet/udpTransport__sendSnapshot.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__sendSnapshot
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.timer
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__expectAck
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__forgetAck
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__writeAll
public import KvNet.Spec.go_etcd_io.raft.v3.node__ReportSnapshot

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

theorem udpTransport.sendSnapshot.wp_proof
    (wp_expectAck : udpNet.expectAck.spec (GF := GF) (hG := hG))
    (wp_forgetAck : udpNet.forgetAck.spec (GF := GF) (hG := hG))
    (wp_writeAll : udpTransport.writeAll.spec (GF := GF) (hG := hG))
    (wp_timer : timer.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : node.ReportSnapshot.spec (GF := GF) (hG := hG)) :
    udpTransport.sendSnapshot.spec (GF := GF) (hG := hG) := by
  intro F γu t γ N id n to seq dsl ds
  wp_start as ⟨#Ht, #Hdsl, #Hdgs⟩
  ihave #Ht' := Ht
  iunfold isUdpCore at Ht'
  icases Ht' with ⟨%sc, %γsc, #Hb, #Hnode, #Hn, %Htr⟩
  ihave #Hb0 := Hb
  iunfold isUdpBase at Hb
  icases Hb with ⟨%u, %boot, %sp, #Hu, #Hun, #Hstats, #Hs, #Hstopc, #HstopB, -⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply_core wp_expectAck F γu u id boot to seq $$ [$Hpkg $Hun]
  iintro %dch ⟨%γd, #Hdone⟩
  wp_auto_lc 2
  irename «try» => Htry
  ihave IH : iprop(∃ k : w64, "Htry" ∷ try_ptr ↦ k ∗ "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1) $$ [Htry Hlc1 Hlc2]
  · iexists W64 0
    iframe Htry
    isplitl [Hlc1]
    · iexact Hlc1
    · iexact Hlc2
  wp_for IH
  wp_if_destruct
  · -- another try
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply wp_writeAll F γu t id sc γsc to dsl DFrac.discard ds $$ [$Hpkg $Hb0 $Hdsl $Hdgs] as %okw -
      wp_apply wp_timer as %tc ⟨%γt, #Htc⟩
      try wp_auto
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the ack
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hdone
        iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
        iintro ⟨-, -⟩
        try wp_auto
        wp_apply wp_add sp (W64 17) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_add sp (W64 33) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_ReportSnapshot n γ N id to _ Htr $$ [$Hraft $Hn]
        try wp_auto
        wp_for_post
        try wp_auto
        wp_apply wp_forgetAck F γu u id boot seq $$ [$Hpkg $Hun]
        try wp_auto
        iapply HΦ
        itrivial
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the timer: another try
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, tc, γt
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Htc
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htc
        inext
        iintro %x -
        wp_auto_lc 2
        wp_for_post
        iframe
        iexists _
        iframe
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- stopped
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
        wp_apply wp_forgetAck F γu u id boot seq $$ [$Hpkg $Hun]
        try wp_auto
        iapply HΦ
        itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · try wp_auto
      wp_apply wp_add sp (W64 34) (by decide) (by decide) $$ [$Hpkg $Hs]
      try wp_auto
      wp_apply wp_writeAll F γu t id sc γsc to dsl DFrac.discard ds $$ [$Hpkg $Hb0 $Hdsl $Hdgs] as %okw -
      wp_apply wp_timer as %tc ⟨%γt, #Htc⟩
      try wp_auto
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the ack
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hdone
        iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
        iintro ⟨-, -⟩
        try wp_auto
        wp_apply wp_add sp (W64 17) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_add sp (W64 33) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_ReportSnapshot n γ N id to _ Htr $$ [$Hraft $Hn]
        try wp_auto
        wp_for_post
        try wp_auto
        wp_apply wp_forgetAck F γu u id boot seq $$ [$Hpkg $Hun]
        try wp_auto
        iapply HΦ
        itrivial
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the timer: another try
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, tc, γt
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Htc
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htc
        inext
        iintro %x -
        wp_auto_lc 2
        wp_for_post
        iframe
        iexists _
        iframe
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- stopped
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
        wp_apply wp_forgetAck F γu u id boot seq $$ [$Hpkg $Hun]
        try wp_auto
        iapply HΦ
        itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
  · try wp_auto
    wp_apply wp_add sp (W64 35) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    wp_apply wp_ReportSnapshot n γ N id to _ Htr $$ [$Hraft $Hn]
    try wp_auto
    wp_apply wp_forgetAck F γu u id boot seq $$ [$Hpkg $Hun]
    try wp_auto
    iapply HΦ
    itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
