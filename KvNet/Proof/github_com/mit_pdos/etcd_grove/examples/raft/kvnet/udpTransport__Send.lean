/-
The proof of `KvNet/Spec/.../kvnet/udpTransport__Send.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__Send
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport__dropped
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

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

theorem udpTransport.Send.wp_proof
    (wp_dropped : udpTransport.dropped.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    udpTransport.Send.spec (GF := GF) (hG := hG) := by
  intro F γu t γ N id n msl dqs ms
  wp_start as ⟨#Ht, Hms, Hel⟩
  ihave #Ht' := Ht
  iunfold isUdpCore at Ht'
  icases Ht' with ⟨%sc, %γsc, #Hb, -⟩
  iunfold isUdpBase at Hb
  icases Hb with ⟨%u, %boot, %sp, -, -, -, -, -, -, #Hps⟩
  iunfold isUdpPeers at Hps
  icases Hps with ⟨%pm, %M, #Hpm, #HM, #Hpeers⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  ihave %Hmslen := ownSlice_len $$ Hms
  ihave IH : iprop(∃ (k : w64) (mv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗ "Hms" ∷ msl ↦*{dqs} ms ∗
      "Hel" ∷ ([∗list] m ∈ ms.drop (sint.nat k), sendElem F m) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ms.length : Int)⌝) $$ [i m Hms Hel]
  · iexists W64 0, _
    iframe i m Hms
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe Hel
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ms.length := by word
    obtain ⟨q, Hq⟩ : ∃ q, ms[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z msl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index msl (sint.Z k) _ dqs q Hk.1 $$ [Hms] as Hms
    · iframe Hms; ipureintro; exact Hq
    have Hdrop : ms.drop (sint.nat k) = q :: ms.drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]
      rw [List.getElem?_eq_getElem Hlt] at Hq
      rw [Option.some.inj Hq]
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [Hdrop]
    icases Hel with ⟨Hq, Hel⟩
    iunfold sendElem at Hq
    icases Hq with ⟨%dq, %dqe, %cap, %st, %src, Hm, #Hok⟩
    try wp_auto
    wp_apply wp_GetTo.1 q _ _ _ _ $$ [$Hpb $Hm] as Hm
    wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpPeer.ty)
      pm M st.msg.To' DFrac.discard) $$ HM as -
    try wp_auto
    cases Hl : M !! st.msg.To' with
    | none =>
      simp only [Option.isSome_none, Option.getD_none]
      try wp_auto
      wp_apply wp_dropped F γu t γ N id n q dq dqe cap st $$ [$Hpkg $Ht $Hm] as -
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, q
      rw [Hk1]
      iframe
      ipureintro; constructor <;> word
    | some p =>
      simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
      try wp_auto
      ihave #Hp := BigSepM.bigSepM_lookup Hl $$ Hpeers
      iunfold isUdpPeer at Hp
      icases Hp with ⟨#Hpid, %ch, %γq, #Hch, #Hbag⟩
      try wp_auto
      ihave #Hisch := is_bag_is_chan γq ch (qElem F st.msg.To') $$ Hbag
      ihave Hqe : qElem F st.msg.To' q $$ [Hm]
      · iunfold qElem
        iexists dq, dqe, cap, st, src
        iframe Hm Hok
        ipureintro; rfl
      wp_bind (App (Val (GoInstruction SelectStmt)) _)
      iapply chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.nonblockingClausePre]
          iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γq, q
          isplit
          · ipureintro; exact ⟨rfl, rfl⟩
          isplit
          · iexact Hisch
          unfold nonblockingSendAu
          isplit
          · iapply bag_nb_send_au_now γq ch (qElem F st.msg.To') q $$ Hbag Hqe
            try wp_auto
            wp_for_post
            iframe
            iexists k + W64 1, q
            rw [Hk1]
            iframe
            ipureintro; constructor <;> word
          · itrivial
        · iapply BigAndL.bigAndL_nil.2
          itrivial
      · iunfold qElem at Hqe
        icases Hqe with ⟨%dq', %dqe', %cap', %st', %src', Hm, -, -⟩
        try wp_auto
        wp_apply wp_dropped F γu t γ N id n q dq' dqe' cap' st' $$ [$Hpkg $Ht $Hm] as -
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, q
        rw [Hk1]
        iframe
        ipureintro; constructor <;> word
  · try wp_auto
    iapply HΦ
    iexact Hms

end proof

end raft_kvnet
end EtcdGrove
end Perennial
