/-
The proof of `KvRaft/Spec/.../kvraft/timer.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.timer
public import Perennial.Proof.time.Link

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
  ipersist c
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

end kvraft
end EtcdGrove
end Perennial
