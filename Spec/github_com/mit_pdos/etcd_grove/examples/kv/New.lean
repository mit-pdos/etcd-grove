/- Lean-first (no Rocq counterpart).

`New(id, node, storage, send)` (kv.go:96): replica `id` on its running node (the driver's token
idle at its start on the store's storage, and the node's view of its configuration, `nodeConfig`)
of the store's cluster (`kvCluster`, 2026-10-28: raft's cluster with snapshots and reconfiguration;
2026-10-27 to 2026-10-28 raft's static cluster, `isStaticCluster`; until then raft's static mode,
`KVStat`), and its storage; it starts `run`. The replica's
seq token (`id ↪[γr.seq] 0`, from the cluster's allocation) starts its sequence numbers. (D22
S-r, 2026-10-21) And what `run` holds of the storage to install and take snapshots (`runStor`: its
snapshot token at the fresh storage, its certificate registry, its voters).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev New.spec : Prop :=
  ∀ (γr : RKVNames) (id : w64) (n st : Loc) (send : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ rkvInv γr ∗
      -- node `id` of the store's cluster, its driver token idle at its start on the store's
      -- storage, its view of its configuration at the voters' membership, nothing applied
      isNode n γr.cluster kvRaftN id ∗
      nodeDriver n γr.cluster kvRaftN (NodeDriverState.init (kvStorIface st)) ∗
      nodeConfig n γr.cluster kvRaftN ⟨0, kvMembership⟩ ∗
      kvCluster γr ∗
      leaderTransferOn γr.cluster kvRaftN ∗
      (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗ id ↪[γr.seq] (W64 0) ∗
      -- the storage's snapshot token, for `run` (`runStor`)
      runStor γr st memStorEmpty ∗
      sendSpec send γr.cluster }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.New))
      (Val #id)) (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n))) (Val #st))
      (Val #send))
  {{ (r : Loc), RET #r; ∃ γp : RepNames, isKV γr γp r }}

end spec

end kv
end EtcdGrove
end Perennial
