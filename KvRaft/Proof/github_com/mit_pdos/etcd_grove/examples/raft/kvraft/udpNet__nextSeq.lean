/-
The proof of `KvRaft/Spec/.../kvraft/udpNet__nextSeq.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__nextSeq
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpSendLemmas

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

theorem udpNet.nextSeq.wp_proof :
    udpNet.nextSeq.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot
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
  wp_if_destruct
  · try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hsq Hctr Hkm HK HKs]
    · inext
      iunfold udpNetLockInv
      iexists _, km, K
      iframe
    try wp_auto
    iapply HΦ
    ileft; ipureintro; rfl
  · have hlt : uint.nat sq < uint.nat (sq + 1) := by
      have : sq ≠ W64 18446744073709551615 := by assumption
      word
    imod udp_seq_fresh γu id boot sq hlt ⊤ (by simp) $$ Hinv Hctr with ⟨Hctr, Htok⟩
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hsq Hctr Hkm HK HKs]
    · inext
      iunfold udpNetLockInv
      iexists sq + 1, km, K
      iframe
    try wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    rw [show sq + W64 1 = sq + 1 from rfl]
    iexact Htok

end proof

end kvraft
end EtcdGrove
end Perennial
