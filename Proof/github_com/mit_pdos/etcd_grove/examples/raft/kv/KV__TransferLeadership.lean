/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kv/KV__TransferLeadership.lean`.
Lean-first (no Rocq counterpart), 2026-10-13.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kv.KV__TransferLeadership

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]
variable [KVStor GF]

theorem KV.TransferLeadership.wp_proof
    (wp_node_TransferLeadership : node.TransferLeadership.spec (GF := GF) (hG := hG)) :
    KV.TransferLeadership.spec (GF := GF) (hG := hG) := by
  intro γr γp r to
  wp_start as #Hreg
  iunfold isKV at Hreg
  icases Hreg with ⟨%id, %n, %st, #Hrep⟩
  iunfold isReplica at Hrep
  iNamed Hrep
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  ihave #Hbg := nodeCtx_background (GF := GF) bgCd
  ihave %Htr0 := kvCluster_untraced γr $$ Hcl
  wp_apply wp_node_TransferLeadership n γr.cluster kvRaftN id id to context.backgroundCtxVal bgCd Htr0
    $$ [$Hraftinit $HisNode $Hbg]
  iapply HΦ
  itrivial

end proof

end raft_kv
end EtcdGrove
end Perennial
