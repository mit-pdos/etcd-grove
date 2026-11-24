/-
The proof of `KvNet/Spec/.../kvnet/udpNet__handle.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__handle
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getDatagram
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMsg
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler__remember
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__ack
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__acked
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType

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

theorem udpNet.handle.wp_proof
    (wp_getDatagram : getDatagram.spec (GF := GF) (hG := hG))
    (wp_acked : udpNet.acked.spec (GF := GF) (hG := hG))
    (wp_add : reassembler.add.spec (GF := GF) (hG := hG))
    (wp_remember : reassembler.remember.spec (GF := GF) (hG := hG))
    (wp_ack : udpNet.ack.spec (GF := GF) (hG := hG))
    (wp_getMsg : getMsg.spec (GF := GF) (hG := hG))
    (wp_add_Stats : Stats.add.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)) :
    udpNet.handle.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot nd sp r stm Q b q bs
  wp_start as ⟨#Hu, #Hsp, #Hs, Hr, #Hstm, #HQ, Hb, #Hdg⟩
  ihave #Hu' := Hu
  iunfold isUdpNet at Hu'
  icases Hu' with ⟨%c, %s, %a, %am, %A, #Hid, #Hconn, #Hca, #Hainv, #Ham, #HA, -, #Hboot, -, -⟩
  ihave #Hdg' := Hdg
  iunfold udpDgOk at Hdg'
  icases Hdg' with ⟨%dg, %Hparse, #Hdgm⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_getDatagram b q bs $$ [$Hpkg $Hb] as %d %ok ⟨Hb, Hd⟩
  rw [Hparse]
  icases Hd with ⟨%Hok, Hd⟩
  subst Hok
  try wp_auto
  wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64
    (go.GoType.PointerType net.UDPAddr.ty) am A d.from' DFrac.discard) $$ HA as -
  try wp_auto
  -- malformed, misaddressed, from an unknown replica or itself: dropped
  wp_if_destruct
  all_goals try wp_if_destruct
  all_goals try wp_if_destruct
  all_goals try (wp_apply wp_add_Stats sp (W64 31) (by decide) (by decide) $$ [$Hpkg $Hs]
                 try wp_auto
                 iapply HΦ
                 iframe; done)
  iunfold dgOwn at Hd
  icases Hd with ⟨%Hdeq, Hch⟩
  obtain ⟨Hkind, Hfrom, Hto, Hboot', Hseq, Hidx, Htot⟩ := Hdeq
  wp_if_destruct
  · -- an ack: wakes its waiter, if any
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply wp_acked F γu u _ _ d.from' d.seq' $$ [$Hpkg $Hu] as %ackd -
      try wp_auto
      cases ackd
      · try wp_auto
        iapply HΦ; iframe
      · try wp_auto
        wp_apply wp_add_Stats sp (W64 37) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        iapply HΦ; iframe
    · try wp_auto
      iapply HΦ; iframe
  · -- a fragment
    iunfold udpDgMOk at Hdgm
    icases Hdgm with (%Hack | ⟨%Hfrag, #Hfok⟩)
    · exfalso; apply Hif; rw [Hkind, Hack]; rfl
    wp_apply wp_add_Stats sp (W64 25) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    ihave Hd : dgOwn d dg $$ [Hch]
    · iunfold dgOwn
      iframe Hch
      ipureintro; exact ⟨Hkind, Hfrom, Hto, Hboot', Hseq, Hidx, Htot⟩
    wp_apply wp_add F γu r d dg $$ [$Hpkg $Hr $Hd $Hfok] as %body %complete %reack ⟨Hr, Hres⟩
    · ipureintro; exact Hfrag
    try wp_auto
    -- a snapshot completed before: acknowledged again
    cases reack
    all_goals try wp_auto
    rotate_left
    wp_apply wp_ack F γu u _ _ nd sp d.from' d.boot' d.seq' $$ [$Hpkg $Hu $Hsp $Hs]
    all_goals try wp_auto
    all_goals
      icases Hres with (%Hc | ⟨%Hc, %bs', Hbody, #Hat, #Hbok⟩) <;> subst Hc
      · try wp_auto
        iapply HΦ; iframe
      iunfold udpBodyOk at Hbok
      icases Hbok with ⟨%src, %st, %Hst, #Hmsg⟩
      obtain ⟨Hst, -⟩ := Hst
      subst Hst
      ihave %Hwf := F.msgOk_wf src st $$ Hmsg
      try wp_auto
      wp_apply wp_getMsg body st Hwf $$ [$Hpkg $Hbody] as %ml Hm
      try wp_auto
      wp_apply wp_GetTo.1 ml _ _ _ _ $$ [$Hpb $Hm] as Hm
      try wp_auto
      wp_if_destruct
      · -- for this replica: queued to its sender's stepper
        wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hpb $Hm] as Hm
        try wp_auto
        wp_apply wp_remember F γu r d.from' _ _ $$ [$Hpkg $Hr] as Hr
        try wp_auto
        wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64
          (go.GoType.ChannelType go.ChanDir.sendrecv
            github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received.ty)
          stm Q d.from' DFrac.discard) $$ Hstm as -
        try wp_auto
        cases hq : Q !! d.from' with
        | none =>
          simp only [Option.isSome_none, Option.getD_none]
          try wp_auto
          wp_apply wp_add_Stats sp (W64 31) (by decide) (by decide) $$ [$Hpkg $Hs]
          try wp_auto
          iapply HΦ; iframe
        | some ch =>
          simp only [Option.isSome_some, Option.getD_some, decide_true]
          try wp_auto
          icases BigSepM.bigSepM_lookup hq $$ HQ with ⟨%γq, #Hbag⟩
          ihave #Hisch := is_bag_is_chan γq ch _ $$ Hbag
          ihave Hel : recvElem F d.to'
              { m' := ml, from' := d.from', boot' := d.boot', seq' := d.seq',
                snap' := decide (st.msg.Type' = W32 7) } $$ [Hm]
          · iunfold recvElem
            iexists src, st
            iframe Hm Hmsg
            ipureintro; exact Hif
          wp_bind (App (Val (GoInstruction SelectStmt)) _)
          iapply chan.wp_select_nonblocking
          isplit
          · iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.nonblockingClausePre]
              iexists github_com.mit_pdos.etcd_grove.examples.raft.kvnet.received, inferInstance,
                inferInstance, inferInstance, inferInstance, ch, γq, _
              isplit
              · ipureintro; exact ⟨rfl, rfl⟩
              isplit
              · iexact Hisch
              unfold nonblockingSendAu
              isplit
              · iapply queue_nb_send_au γq ch (recvElem F d.to') _ $$ Hbag Hel
                try wp_auto
                iapply HΦ
                iframe
              · itrivial
            · iapply BigAndL.bigAndL_nil.2
              itrivial
          · try wp_auto
            wp_apply wp_add_Stats sp (W64 38) (by decide) (by decide) $$ [$Hpkg $Hs]
            try wp_auto
            iapply HΦ; iframe
      · -- not for this replica: dropped
        try wp_auto
        wp_apply wp_remember F γu r d.from' _ _ $$ [$Hpkg $Hr] as Hr
        try wp_auto
        wp_apply wp_add_Stats sp (W64 31) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        iapply HΦ; iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
