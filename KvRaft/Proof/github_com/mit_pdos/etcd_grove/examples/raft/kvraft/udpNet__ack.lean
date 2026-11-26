/-
The proof of `KvRaft/Spec/.../kvraft/udpNet__ack.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__ack
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats__add
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putAck
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__write

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

theorem udpNet.ack.wp_proof
    (wp_putAck : putAck.spec (GF := GF) (hG := hG))
    (wp_write : udpNet.write.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    udpNet.ack.spec (GF := GF) (hG := hG) := by
  intro F γu u id boot nd sp to b seq
  wp_start as ⟨#Hu, #Hsp, #Hs⟩
  ihave #Hu' := Hu
  iunfold isUdpNet at Hu'
  icases Hu' with ⟨%c, %s, %a, %am, %A, #Hid, -⟩
  try wp_auto
  wp_apply wp_putAck id to b seq $$ [$Hpkg] as %sl ⟨Hsl, -⟩
  imod ownSlice_persist sl _ _ $$ Hsl with #Hsl
  wp_apply wp_write F γu u id boot to sl (ackBytes id to b seq) $$ [$Hpkg $Hu $Hsl] as %ok -
  · iunfold udpDgOk
    iexists _
    isplit
    · ipureintro; exact parseDg_ackBytes id to b seq
    iunfold udpDgMOk
    ileft
    ipureintro; rfl
  try wp_auto
  cases ok
  · try wp_auto
    wp_apply wp_add sp (W64 32) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    iapply HΦ; itrivial
  · try wp_auto
    wp_apply wp_add sp (W64 36) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    iapply HΦ; itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
