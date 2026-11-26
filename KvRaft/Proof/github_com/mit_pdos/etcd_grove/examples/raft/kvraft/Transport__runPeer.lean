/-
The proof of `KvRaft/Spec/.../kvraft/Transport__runPeer.lean`: a loop selecting on the queue (the
bag's receive: never closed) and the stop channel (2026-11-24, G5: the broadcast's receive, which
closes the connection, if any, and returns), its credits for the bag's receive in the invariant, its invariant the connection variable: `nil`, or a connection to
the peer's address whose dialer's stream so far is the hello byte and whole frames of messages with
their facts (`sendTok cn false (kvP F pid) (helloPeerB :: framesBytes sts)`). A message's frame is
admitted by the protocol (`peer_send`), written through `write_acc`'s accessor; a write in time
extends the stream by the frame, any failure closes the connection (`close_au`, through `connIs`)
and drops the message.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__runPeer
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__dial
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__dropped
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats__add
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.closeAfter
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.writeFrame
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putMsg
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import KvRaft.Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import KvRaft.Spec.net.Conn__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions]

theorem Transport.runPeer.wp_proof (wp_dial : Transport.dial.spec (GF := GF) (hG := hG))
    (wp_dropped : Transport.dropped.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_closeAfter : closeAfter.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_putMsg : putMsg.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    Transport.runPeer.spec (GF := GF) (hG := hG) := by
  intro F t γ N id n p pid a et ed
  wp_start as ⟨#Ht, #Hp, #Het, #Hed⟩
  ihave #Ht' := Ht
  iunfold isTransportCore at Ht'
  icases Ht' with ⟨%sp, %sc, %γsc, #Hid, #Hnode, #Hstats, #Hs, #Hn, %Htr, #Hstop⟩
  iunfold isTransportStop at Hstop
  icases Hstop with ⟨#Hstopc, #HstopB⟩
  iunfold isPeer at Hp
  icases Hp with ⟨#Hpa, %ch, %γq, #Hch, #Hbag⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto_lc 2
  ihave IH : iprop(∃ (cv : GoInterface),
      "c" ∷ c_ptr ↦ cv ∗ "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 ∗
      "Hc" ∷ (⌜cv = interface.nil⌝ ∨ ∃ (cn : Nat) (sts : List (w64 × MsgSt)),
        net.isConn (GF := GF) cv cn false a ∗
        sendTok cn false (kvP F pid) (helloPeerB :: framesBytes sts) ∗
        ([∗list] q ∈ sts, F.msgOk q.1 q.2) ∗ ⌜∀ q ∈ sts, (encMsg q.2).length < 2 ^ 63⌝ ∗
        connIs cn)) $$ [c Hlc1 Hlc2]
  · iexists _
    iframe c Hlc1 Hlc2
    ileft; ipureintro; rfl
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
    icases Hc with (%Hnil | HC)
    · subst Hnil
      try wp_auto
      wp_apply wp_dial F t γ N id n p pid a et ed $$ [$Hpkg $Ht $Hpa $Het $Hed] as %c' Hc'
      try wp_auto
      icases Hc' with (%Hc'nil | ⟨%cn, #Hconn, HW, -, #Hci⟩)
      · subst Hc'nil
        try wp_auto
        wp_apply wp_dropped F t γ N id n mq dq dqe cap st $$ [$Hpkg $Ht $Hm] as -
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ileft; ipureintro; rfl
      ihave #Hconn' := Hconn
      iunfold net.isConn at Hconn'
      icases Hconn' with ⟨%tc, %la, %ra, %Hct, #Hcat⟩
      subst Hct
      try wp_auto
      rw [show [helloPeerB] = helloPeerB :: framesBytes ([] : List (w64 × MsgSt)) by simp [framesBytes]] at *
      ihave #Hsts : ([∗list] q ∈ ([] : List (w64 × MsgSt)), F.msgOk q.1 q.2) $$ []
      · iapply BigSepL.bigSepL_nil.2; iempintro
      have Hstsl : ∀ q ∈ ([] : List (w64 × MsgSt)), (encMsg q.2).length < 2 ^ 63 := by simp
      generalize ([] : List (w64 × MsgSt)) = sts at *
      ihave #Hca := cAcc_of_connIs cn false $$ Hci
      wp_apply wp_closeAfter _ cn false a _ iprop(True) $$ [] as %disarm #Hdis
      · iframe Hconn
        isplitl []
        · itrivial
        imodintro
        iintro -
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      ihave Hns := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
      ihave Hnc := ownSliceCap_nil (V := w8) (GF := GF)
      wp_apply wp_putMsg slice.nil [] mq dq dqe cap st $$ [$Hpkg $Hns $Hnc $Hm] as %s1 ⟨Hs1, -, Hm⟩
      rw [List.nil_append]
      ihave %Hs1l := ownSlice_len $$ Hs1
      have Hlen : ((encMsg st).length : Int) < 2 ^ 63 := by have := Hs1l.1; have := Hs1l.2; word
      try wp_auto
      ihave HW := writeP_init cn false (kvP F pid) _ $$ HW
      ihave #Hpr : □ kvP F pid cn ((helloPeerB :: framesBytes sts) ++ putB (encMsg st)) $$ []
      · imodintro
        rw [List.cons_append, show framesBytes sts ++ putB (encMsg st) = framesBytes (sts ++ [(src, st)]) from
            (framesBytes_snoc sts (src, st)).symm]
        iapply peer_send F pid cn sts src st Hstsl (by omega) $$ Hsts Hok
      ihave #Hacc := write_acc cn false (kvP F pid) (helloPeerB :: framesBytes sts) (putB (encMsg st)) $$ Hpr
      wp_apply wp_writeFrame _ cn false a s1 (encMsg st) (DFrac.own 1) ed
          (fun w res => writeP cn false (kvP F pid) (helloPeerB :: framesBytes sts) w res)
          $$ [Hs1 HW] as %ok1 ⟨%w1, %res1, HW, -, %Hw1⟩
      · iframe Hconn Hs1 Hed HW
        iexact Hacc
      try wp_auto
      wp_bind (App (Val #disarm) (Val #()))
      iapply Hdis
      iintro %inTime -
      cases inTime <;> cases ok1
      all_goals try wp_auto
      any_goals
        wp_apply wp_add sp (W64 21) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_Close tc cn false a la ra (fun _ => iprop(True)) $$ [] as %err' -
        · iframe Hcat
          iunfold cAcc at Hca
          iexact Hca
        try wp_auto
        wp_apply wp_dropped F t γ N id n mq dq dqe cap st $$ [$Hpkg $Ht $Hm] as -
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ileft; ipureintro; rfl
      obtain ⟨-, Hw, -⟩ := Hw1
      have Hw := Hw rfl
      subst Hw
      wp_apply wp_add sp (W64 17) (by decide) (by decide) $$ [$Hpkg $Hs]
      try wp_auto
      wp_apply wp_GetType.1 mq _ _ _ _ $$ [$Hpb $Hm] as Hm
      try wp_auto
      ihave HW : sendTok cn false (kvP F pid) (helloPeerB :: framesBytes (sts ++ [(src, st)])) $$ [HW]
      · unfold writeP
        rw [List.cons_append, show framesBytes sts ++ putB (encMsg st) = framesBytes (sts ++ [(src, st)]) from
          (framesBytes_snoc sts (src, st)).symm]
        iexact HW
      have Hstsl' : ∀ q ∈ sts ++ [(src, st)], (encMsg q.2).length < 2 ^ 63 := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact Hstsl q hq
        · rw [List.mem_singleton] at hq; subst hq; simp only; omega
      ihave #Hsts' : ([∗list] q ∈ sts ++ [(src, st)], F.msgOk q.1 q.2) $$ []
      · iapply BigSepL.bigSepL_append.2
        iframe Hsts
        iapply BigSepL.bigSepL_singleton.2
        iexact Hok
      wp_if_destruct
      · wp_apply wp_add sp (W64 2) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_GetTo.1 mq _ _ _ _ $$ [$Hpb $Hm] as Hm
        try wp_auto
        wp_apply wp_ReportSnapshot n γ N id st.msg.To' _ Htr $$ [$Hraft $Hn]
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        iright
        iexists cn, sts ++ [(src, st)]
        iframe Hconn HW Hsts' Hci
        ipureintro; exact Hstsl'
      · wp_for_post
        iframe
        iexists _
        iframe
        iright
        iexists cn, sts ++ [(src, st)]
        iframe Hconn HW Hsts' Hci
        ipureintro; exact Hstsl'
    · icases HC with ⟨%cn, %sts, #Hconn, HW, #Hsts, %Hstsl, #Hci⟩
      ihave #Hconn' := Hconn
      iunfold net.isConn at Hconn'
      icases Hconn' with ⟨%tc, %la, %ra, %Hct, #Hcat⟩
      subst Hct
      try wp_auto
      ihave #Hca := cAcc_of_connIs cn false $$ Hci
      wp_apply wp_closeAfter _ cn false a _ iprop(True) $$ [] as %disarm #Hdis
      · iframe Hconn
        isplitl []
        · itrivial
        imodintro
        iintro -
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      ihave Hns := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
      ihave Hnc := ownSliceCap_nil (V := w8) (GF := GF)
      wp_apply wp_putMsg slice.nil [] mq dq dqe cap st $$ [$Hpkg $Hns $Hnc $Hm] as %s1 ⟨Hs1, -, Hm⟩
      rw [List.nil_append]
      ihave %Hs1l := ownSlice_len $$ Hs1
      have Hlen : ((encMsg st).length : Int) < 2 ^ 63 := by have := Hs1l.1; have := Hs1l.2; word
      try wp_auto
      ihave HW := writeP_init cn false (kvP F pid) _ $$ HW
      ihave #Hpr : □ kvP F pid cn ((helloPeerB :: framesBytes sts) ++ putB (encMsg st)) $$ []
      · imodintro
        rw [List.cons_append, show framesBytes sts ++ putB (encMsg st) = framesBytes (sts ++ [(src, st)]) from
            (framesBytes_snoc sts (src, st)).symm]
        iapply peer_send F pid cn sts src st Hstsl (by omega) $$ Hsts Hok
      ihave #Hacc := write_acc cn false (kvP F pid) (helloPeerB :: framesBytes sts) (putB (encMsg st)) $$ Hpr
      wp_apply wp_writeFrame _ cn false a s1 (encMsg st) (DFrac.own 1) ed
          (fun w res => writeP cn false (kvP F pid) (helloPeerB :: framesBytes sts) w res)
          $$ [Hs1 HW] as %ok1 ⟨%w1, %res1, HW, -, %Hw1⟩
      · iframe Hconn Hs1 Hed HW
        iexact Hacc
      try wp_auto
      wp_bind (App (Val #disarm) (Val #()))
      iapply Hdis
      iintro %inTime -
      cases inTime <;> cases ok1
      all_goals try wp_auto
      any_goals
        wp_apply wp_add sp (W64 21) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_Close tc cn false a la ra (fun _ => iprop(True)) $$ [] as %err' -
        · iframe Hcat
          iunfold cAcc at Hca
          iexact Hca
        try wp_auto
        wp_apply wp_dropped F t γ N id n mq dq dqe cap st $$ [$Hpkg $Ht $Hm] as -
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ileft; ipureintro; rfl
      obtain ⟨-, Hw, -⟩ := Hw1
      have Hw := Hw rfl
      subst Hw
      wp_apply wp_add sp (W64 17) (by decide) (by decide) $$ [$Hpkg $Hs]
      try wp_auto
      wp_apply wp_GetType.1 mq _ _ _ _ $$ [$Hpb $Hm] as Hm
      try wp_auto
      ihave HW : sendTok cn false (kvP F pid) (helloPeerB :: framesBytes (sts ++ [(src, st)])) $$ [HW]
      · unfold writeP
        rw [List.cons_append, show framesBytes sts ++ putB (encMsg st) = framesBytes (sts ++ [(src, st)]) from
          (framesBytes_snoc sts (src, st)).symm]
        iexact HW
      have Hstsl' : ∀ q ∈ sts ++ [(src, st)], (encMsg q.2).length < 2 ^ 63 := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact Hstsl q hq
        · rw [List.mem_singleton] at hq; subst hq; simp only; omega
      ihave #Hsts' : ([∗list] q ∈ sts ++ [(src, st)], F.msgOk q.1 q.2) $$ []
      · iapply BigSepL.bigSepL_append.2
        iframe Hsts
        iapply BigSepL.bigSepL_singleton.2
        iexact Hok
      wp_if_destruct
      · wp_apply wp_add sp (W64 2) (by decide) (by decide) $$ [$Hpkg $Hs]
        try wp_auto
        wp_apply wp_GetTo.1 mq _ _ _ _ $$ [$Hpb $Hm] as Hm
        try wp_auto
        wp_apply wp_ReportSnapshot n γ N id st.msg.To' _ Htr $$ [$Hraft $Hn]
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        iright
        iexists cn, sts ++ [(src, st)]
        iframe Hconn HW Hsts' Hci
        ipureintro; exact Hstsl'
      · wp_for_post
        iframe
        iexists _
        iframe
        iright
        iexists cn, sts ++ [(src, st)]
        iframe Hconn HW Hsts' Hci
        ipureintro; exact Hstsl'

  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed: close the connection, if any, and return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γsc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    try wp_auto
    icases Hc with (%Hnil | ⟨%cn, %sts, #Hconn, HW, #Hsts, %Hstsl, #Hci⟩)
    · subst Hnil
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ
      itrivial
    · ihave #Hconn' := Hconn
      iunfold net.isConn at Hconn'
      icases Hconn' with ⟨%tc, %la, %ra, %Hct, #Hcat⟩
      subst Hct
      try wp_auto
      ihave #Hca := cAcc_of_connIs cn false $$ Hci
      wp_apply wp_Close tc cn false a la ra (fun _ => iprop(True)) $$ [] as %err' -
      · iframe Hcat
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ
      itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
