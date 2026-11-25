/-
The proof of `KvNet/Spec/.../kvnet/listenUDP.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listenUDP
public import KvNet.Spec.net.ListenUDP
public import Perennial.Proof.time.Link

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

theorem listenUDP.wp_proof
    (wp_ListenUDP : net.ListenUDP.spec (GF := GF) (hG := hG)) :
    listenUDP.spec (GF := GF) (hG := hG) := by
  intro p ip port a
  wp_start as ⟨#Hp, %Hv⟩
  try wp_auto
  wp_for
  wp_apply wp_ListenUDP p ip port a $$ [] as %c %err (⟨%Herr, %s, #Hc⟩ | ⟨%Hcn, #Herr⟩)
  · iframe Hp
    ipureintro; exact Hv
  · subst Herr
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    iexists s
    iexact Hc
  · iunfold net.udpListenErr at Herr
    icases Herr with ⟨%pe, %e, %Herr, -, -⟩
    subst Herr
    try wp_auto
    wp_apply time.wp_Sleep
    try wp_auto
    wp_for_post
    iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
