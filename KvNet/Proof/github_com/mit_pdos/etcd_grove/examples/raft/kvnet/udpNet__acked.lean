/-
The proof of `KvNet/Spec/.../kvnet/udpNet__acked.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__acked

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

theorem udpNet.acked.wp_proof :
    udpNet.acked.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot src seq
  wp_start as #Hu
  iunfold isUdpNet at Hu
  icases Hu with ⟨%c, %s, %a, %am, %A, #Hid, #Hc, #Hconn, #Ha, #Ham, #HA, #Haddrs, #Hboot, #Hinv,
    #Hmu⟩
  try wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold udpNetLockInv at HL
  icases HL with ⟨%sq, %km, %K, Hsq, Hctr, Hkm, HK, HKs⟩
  try wp_auto
  wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64
    (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ackWait.ty)
    km K seq (DFrac.own 1)) $$ HK as HK
  try wp_auto
  cases h : K !! seq with
  | none =>
    simp only [Option.isSome_none, Option.getD_none]
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hsq Hctr Hkm HK HKs]
    · inext
      iunfold udpNetLockInv
      iexists sq, km, K
      iframe
    try wp_auto
    iapply HΦ
    itrivial
  | some w =>
    simp only [Option.isSome_some, Option.getD_some, decide_true]
    icases (BigSepM.bigSepM_delete h).1 $$ HKs with ⟨Hw, HKs⟩
    iunfold ackWaitOwn at Hw
    icases Hw with ⟨%wto, %ch, %γch, #Hwto, #Hwdone, Hpend⟩
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply (wp_mapDelete (K := w64) (V := Loc) km K seq go.uint64
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ackWait.ty)) $$ HK
        as HK
      try wp_auto
      ihave #Htt : □ (True : IProp GF) $$ []
      · imodintro; itrivial
      wp_apply wp_broadcast_chan_close ch γch iprop(True) $$ [$Hpend $Htt] as -
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hsq Hctr Hkm HK HKs]
      · inext
        iunfold udpNetLockInv
        iexists sq, km, _
        iframe
      try wp_auto
      iapply HΦ
      itrivial
    · try wp_auto
      ihave HKs : [∗map] k ↦ x ∈ K, ackWaitOwn (GF := GF) x $$ [HKs Hpend]
      · iapply (BigSepM.bigSepM_delete h).2
        iframe HKs
        iunfold ackWaitOwn
        iexists wto, ch, γch
        iframe Hwto Hwdone Hpend
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hsq Hctr Hkm HK HKs]
      · inext
        iunfold udpNetLockInv
        iexists sq, km, K
        iframe
      try wp_auto
      iapply HΦ
      itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
