/-
The proof of `KvRaft/Spec/.../kvraft/udpNet__expectAck.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__expectAck

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
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

theorem udpNet.expectAck.wp_proof :
    udpNet.expectAck.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot to seq
  wp_start as #Hu
  iunfold isUdpNet at Hu
  icases Hu with ⟨%c, %s, %a, %am, %A, #Hid, #Hc, #Hconn, #Ha, #Ham, #HA, #Haddrs, #Hboot, #Hinv,
    #Hmu⟩
  try wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γch ch $$ Hch Hoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close ch γch iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close ch γch iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  try wp_auto
  iStructNamed «$r0»
  ipersist to
  ipersist done
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold udpNetLockInv at HL
  icases HL with ⟨%sq, %km, %K, Hsq, Hctr, Hkm, HK, HKs⟩
  try wp_auto
  wp_apply (wp_mapInsert (K := w64) (V := Loc) go.uint64 km K seq _) $$ HK as HK
  try wp_auto
  ihave Hw : ackWaitOwn (GF := GF) «$r0_ptr» $$ [Hpend]
  · iunfold ackWaitOwn
    iexists to, ch, γch
    iframe to done Hpend
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hsq Hctr Hkm HK HKs Hw]
  · inext
    iunfold udpNetLockInv
    iexists sq, km, _
    iframe Hsq Hctr Hkm HK
    cases h : K !! seq with
    | none =>
      iapply (BigSepM.bigSepM_insert h).2
      iframe Hw HKs
    | some y =>
      icases (BigSepM.bigSepM_delete h).1 $$ HKs with ⟨-, HKs⟩
      iapply BigSepM.bigSepM_insert_delete.2
      iframe Hw HKs
  try wp_auto
  iapply HΦ
  iexists γch
  iexact Hunk

end proof

end kvraft
end EtcdGrove
end Perennial
