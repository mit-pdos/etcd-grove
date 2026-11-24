/-
The proof of `KvNet/Spec/.../kvnet/timer.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.timer
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

theorem timer.wp_proof :
    timer.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  try wp_auto
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %ch %γ ⟨#Hch, %_, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γ Unit (.Buffered []) $$ Hoc
  imod start_bag (fun _ : Unit => iprop(True)) (.Buffered []) ch γ trivial $$ Hch Hoc with #Hbag
  try wp_auto
  wp_apply time.wp_AfterFunc $$ [] as %tm -
  · try wp_auto
    wp_apply wp_bag_send γ ch () (fun _ : Unit => iprop(True)) $$ [$Hbag]
    try wp_auto
    itrivial
  try wp_auto
  iapply HΦ
  iexists γ
  iexact Hbag

end proof

end raft_kvnet
end EtcdGrove
end Perennial
