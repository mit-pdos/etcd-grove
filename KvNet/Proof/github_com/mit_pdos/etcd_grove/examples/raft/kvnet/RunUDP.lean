/-
The proof of `KvNet/Spec/.../kvnet/RunUDP.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RunUDP
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__accept
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listen
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.startNodeUDP
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__receive

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
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [field_sem : net.FieldAssumptions]

theorem RunUDP.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF) (stp : NodeStopper GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF)
    (wp_listen : listen.spec (GF := GF) (hG := hG))
    (wp_startNodeUDP : startNodeUDP.spec (GF := GF) (hG := hG) F rep cf stp S)
    (wp_receive : udpNet.receive.spec (GF := GF) (hG := hG) F rep stp)
    (wp_accept : Node.accept.spec (GF := GF) (hG := hG) F rep stp cf) :
    RunUDP.spec (GF := GF) (hG := hG) F rep cf S := by
  intro γu cfg M a eof ed Hma Hok
  wp_start as ⟨#HM, #Ha, HS, Hu, #Heof, #Hed, #Hcc⟩
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w64) (V := GoString) go.uint64 go.string _ M cfg.ID' DFrac.discard)
    $$ HM as -
  rw [Hma]
  simp only [Option.getD_some]
  try wp_auto
  wp_apply wp_listen a (kvP F cfg.ID') (kvQ F cfg.ID') $$ [$Hpkg $Ha] as %li ⟨%l, #Hli, Hlis, #Hla⟩
  try wp_auto
  wp_apply wp_startNodeUDP γu cfg M a Hma Hok $$ [$Hpkg $HM $HS $Hu]
    as %nd %u ⟨%γ, %N, %boot, #Hnd, #Hcl, #Hun⟩
  try wp_auto
  wp_apply wp_fork $$ []
  · wp_apply wp_receive γu u cfg.ID' boot nd γ N $$ [$Hpkg $Hun $Hnd $Hcc]
    itrivial
  try wp_auto
  wp_apply wp_accept nd γ N cfg.ID' li l a eof ed $$ [$Hpkg $Hnd $Hcl $Ha $Hli $Hlis $Hla $Heof $Hed $Hcc]
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
