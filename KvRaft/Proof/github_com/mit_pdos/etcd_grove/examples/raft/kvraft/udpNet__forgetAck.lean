/-
The proof of `KvRaft/Spec/.../kvraft/udpNet__forgetAck.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__forgetAck

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

theorem udpNet.forgetAck.wp_proof :
    udpNet.forgetAck.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot seq
  wp_start as #Hu
  iunfold isUdpNet at Hu
  icases Hu with ⟨%c, %s, %a, %am, %A, #Hid, #Hc, #Hconn, #Ha, #Ham, #HA, #Haddrs, #Hboot, #Hinv,
    #Hmu⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold udpNetLockInv at HL
  icases HL with ⟨%sq, %km, %K, Hsq, Hctr, Hkm, HK, HKs⟩
  try wp_auto
  wp_apply (wp_mapDelete (K := w64) (V := Loc) km K seq go.uint64
    (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.ackWait.ty)) $$ HK as HK
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hsq Hctr Hkm HK HKs]
  · inext
    iunfold udpNetLockInv
    iexists sq, km, _
    iframe Hsq Hctr Hkm HK
    cases h : K !! seq with
    | none =>
      rw [GMap.delete_notin _ _ h]
      iexact HKs
    | some y =>
      icases (BigSepM.bigSepM_delete h).1 $$ HKs with ⟨-, HKs⟩
      iexact HKs
  try wp_auto
  iapply HΦ
  itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
