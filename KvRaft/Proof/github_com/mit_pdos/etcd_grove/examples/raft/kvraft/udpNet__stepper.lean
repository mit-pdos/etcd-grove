/-
The proof of `KvRaft/Spec/.../kvraft/udpNet__stepper.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__stepper
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__stepPeer
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__ack

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

theorem udpNet.stepper.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (wp_stepPeer : Node.stepPeer.spec (GF := GF) (hG := hG) F rep stp)
    (wp_ack : udpNet.ack.spec (GF := GF) (hG := hG)) :
    udpNet.stepper.spec (GF := GF) (hG := hG) F rep stp := by
  intro γu u id boot nd γ N q γq
  wp_start as ⟨#Hu, #Hnd, #Hcc, #Hq⟩
  ihave #Hnd' := Hnd
  iunfold isNodeS at Hnd'
  icases Hnd' with ⟨%cfg, %M, %sp, %f, -, -, -, #Hst, #Hs, -⟩
  try wp_auto
  ihave IH : iprop(True) $$ []
  · itrivial
  wp_for IH
  wp_apply wp_bag_receive γq q (recvElem F id) $$ Hq as %x Hx
  iunfold recvElem at Hx
  icases Hx with ⟨%src, %st, Hm, #Hok, %HTo⟩
  try wp_auto
  wp_apply wp_stepPeer nd γ N id x.m' src st HTo $$ [$Hpkg $Hnd $Hcc $Hok $Hm]
  try wp_auto
  cases x.snap'
  · try wp_auto
    wp_for_post
    iframe
  · try wp_auto
    wp_apply wp_ack F γu u id boot nd sp x.from' x.boot' x.seq' $$ [$Hpkg $Hu $Hst $Hs]
    try wp_auto
    wp_for_post
    iframe

end proof

end kvraft
end EtcdGrove
end Perennial
