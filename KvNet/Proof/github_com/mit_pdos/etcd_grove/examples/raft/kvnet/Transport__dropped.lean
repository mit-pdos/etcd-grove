/-
The proof of `KvNet/Spec/.../kvnet/Transport__dropped.lean`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport__dropped
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import KvNet.Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import KvNet.Spec.go_etcd_io.raft.v3.node__ReportSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Transport.dropped.wp_proof (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : node.ReportSnapshot.spec (GF := GF) (hG := hG)) :
    Transport.dropped.spec (GF := GF) (hG := hG) := by
  intro F t γ N id n m dq dqe cap st
  wp_start as ⟨#Ht, Hm⟩
  unfold isTransportCore
  icases Ht with ⟨%sp, %sc, %γsc, #Hid, #Hnode, #Hstats, #Hs, #Hn, %Htr, -⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_add sp (W64 19) (by decide) (by decide) $$ [$Hpkg $Hs]
  try wp_auto
  wp_apply wp_GetTo.1 m _ _ _ _ $$ [$Hpb $Hm] as Hm
  try wp_auto
  wp_apply wp_ReportUnreachable n γ N id st.msg.To' $$ [$Hraft $Hn]
  try wp_auto
  wp_apply wp_GetType.1 m _ _ _ _ $$ [$Hpb $Hm] as Hm
  try wp_auto
  wp_if_destruct
  · wp_apply wp_GetTo.1 m _ _ _ _ $$ [$Hpb $Hm] as Hm
    try wp_auto
    wp_apply wp_ReportSnapshot n γ N id st.msg.To' _ Htr $$ [$Hraft $Hn]
    try wp_auto
    iapply HΦ
    iexact Hm
  · iapply HΦ
    iexact Hm

end proof

end raft_kvnet
end EtcdGrove
end Perennial
