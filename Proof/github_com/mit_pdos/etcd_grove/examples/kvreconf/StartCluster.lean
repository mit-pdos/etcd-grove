/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/StartCluster.lean`. Lean-first
(no Rocq counterpart).

The ghost state first: raft's cluster of the voters `vs = bootVoters Voters` (`cluster_alloc`,
`dup = true`), its decisions handed to the store's rule (`confPolicy_alloc`), the next-id bound at
`Voters+1`, the stopper's flag, the store's invariant (`rkvInv_alloc`: every id's read sequence at
`0`) and the snapshot registry. Then the cluster's struct: the bootstrap `ConfState` (the voters
appended, frozen read-only), the `Stats` counters (`isStats_alloc`), `c.mu` locked fresh
(`wp_Mutex_Lock_fresh`: its invariant is due at the `Unlock`). The loop starts each founder as
`startNew` starts a newcomer, with its `nodeFounder` token; the `Unlock` gives the lock its
invariant: the founders' replicas and stop tokens, the ids above them fresh.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.StartCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.MutexFresh
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__config
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__tick
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__sender
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.newReplica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClusterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem StartCluster.wp_proof
    (wp_config : Cluster.config.spec (GF := GF) (hG := hG))
    (wp_tick : Cluster.tick.spec (GF := GF) (hG := hG))
    (wp_sender : Cluster.sender.spec (GF := GF) (hG := hG))
    (wp_newReplica : newReplica.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG))
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG)) :
    StartCluster.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end kvreconf
end EtcdGrove
end Perennial
