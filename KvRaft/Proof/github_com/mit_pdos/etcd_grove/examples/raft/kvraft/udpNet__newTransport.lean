/-
The proof of `KvRaft/Spec/.../kvraft/udpNet__newTransport.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__newTransport
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport__Send
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport__start
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport__stop

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]

theorem udpNet.newTransport.wp_proof
    (wp_start : udpTransport.start.spec (GF := GF) (hG := hG))
    (wp_Send : udpTransport.Send.spec (GF := GF) (hG := hG))
    (wp_stop : udpTransport.stop.spec (GF := GF) (hG := hG)) :
    udpNet.newTransport.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot γ N am M sts Htr
  wp_start as ⟨#Hun, #HM, #Hsts⟩
  ihave #Hu := Hun
  iunfold isUdpNet at Hu
  icases Hu with ⟨%c, %s, %a, %uam, %A, #Hid, #Hc, #Hconn, #Ha, #Ham, #HA, #Haddrs, #Hboot, #Hinv,
    #Hmu⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %pm Hpm
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsc, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsc Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  try wp_auto
  irename : u_ptr ↦ u => Huv
  iStructNamed «$r0»
  ipersist u
  ipersist stats
  ipersist peers
  ipersist stopc
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
      (Mp : GMap w64 Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "t" ∷ t_ptr ↦ «$r0_ptr» ∗
      "Huv" ∷ u_ptr ↦ u ∗
      "pid" ∷ pid_ptr ↦ x ∗
      "Hpm" ∷ pm ↦$ Mp ∗
      "Hps" ∷ ([∗map] k ↦ p ∈ Mp, isUdpPeer F p k))) _ go.uint64 _ uam A DFrac.discard $$ HA
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [pid Hpm t Huv]
  · iexists _, ∅
    simp only [named]
    iframe
    isplitr
    · ipureintro; exact Int.le_refl _
    iapply BigSepM.bigSepM_empty.2; itrivial
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    try wp_auto
    wp_if_destruct
    · -- itself: left out
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, Mp
      simp only [named]
      iframe
      ipureintro; omega
    · -- another replica: its peer
      wp_apply chan.wp_make2 (V := Loc) (W64 256) as %ch %γq ⟨#Hch, %_, Hoc⟩
      · ipureintro; decide
      ihave Hoc : ownChan γq Loc (.Buffered []) $$ Hoc
      imod start_bag (qElem F key) (.Buffered []) ch γq trivial $$ Hch Hoc with #Hbag
      try wp_auto
      iStructNamed «$r0»
      ipersist id
      ipersist queue
      try wp_auto
      wp_apply (wp_mapInsert (K := w64) (V := Loc) go.uint64 pm Mp key _) $$ Hpm as Hpm
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; omega
      ihave #Hp : isUdpPeer F «$r0_ptr» key $$ []
      · unfold isUdpPeer
        iframe id
        iexists ch, γq
        iframe queue Hbag
      cases h : Mp !! key with
      | none =>
        iapply (BigSepM.bigSepM_insert h).2
        iframe Hp Hps
      | some y =>
        icases (BigSepM.bigSepM_delete h).1 $$ Hps with ⟨-, Hps⟩
        iapply BigSepM.bigSepM_insert_delete.2
        iframe Hp Hps
  iintro HP -
  iNamed HP
  imod ownMap_persist pm _ _ $$ Hpm with #Hpm
  try wp_auto
  ihave #Hbase : isUdpBase F γu «$r0_ptr» id sc γsc $$ [Hps]
  · unfold isUdpBase
    iexists u, boot, sts
    iframe #
    unfold isUdpPeers
    iexists pm, Mp
    iframe peers Hpm Hps
  iapply HΦ
  unfold ptFresh
  iexists (⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport.ty,
    #«$r0_ptr»⟩ : GoInterfaceOk)
  isplitr
  · ipureintro; rfl
  iintro %n %Φ' #Hpkg' #HisNode HΦ'
  wp_apply wp_start F γu «$r0_ptr» γ N id n sc γsc $$ [$Hpkg' $Hbase $HisNode node] as #Htc
  · isplitl [node]
    · iexists _; iexact node
    ipureintro; exact Htr
  iapply HΦ'
  unfold ptRunning
  isplitr
  · unfold ptSend
    iexists (⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport.ty,
      #«$r0_ptr»⟩ : GoInterfaceOk)
    isplitr
    · ipureintro; rfl
    iintro !> %msl %dqs %ms %Φs !> ⟨Hpk, Hsl, Hms⟩ HΦs
    iapply wp_Send F γu «$r0_ptr» γ N id n msl dqs ms $$ [$Hpk $Htc $Hsl $Hms]
    iexact HΦs
  · unfold ptStop
    iexists (⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport.ty,
      #«$r0_ptr»⟩ : GoInterfaceOk)
    isplitr
    · ipureintro; rfl
    iintro %Φs HΦs
    iapply wp_stop «$r0_ptr» sc γsc $$ [$Hpkg' $stopc Hpend]
    · unfold transportStopper; iexact Hpend
    inext
    iintro -
    iexact HΦs

end proof

end kvraft
end EtcdGrove
end Perennial
