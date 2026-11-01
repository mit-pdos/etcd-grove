/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__startNew.lean`. Lean-first
(no Rocq counterpart).

Under `c.mu`: with fewer than `maxReplicas` replicas (the map's keys are `1 … nextID-1`, so
`nextID ≤ 9`), the fresh id `nextID` is joined (`joinAuth_join`: not among the started ids), its
storage allocated and registered (`kvrStor_alloc`), its node restarted as a newcomer
(`RestartNode`'s `nodeJoin` disjunct, the bootstrap voters at `0` from the store's cluster), its
transport made (`sender`, `repKnown` from the raised `γr.nid` bound) and the replica started
(`newReplica`, with the id's read-sequence element from the lock's `freshIds`). The replica and its
stop tokens (unless the stopper took them) go into the lock.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__startNew
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

theorem Cluster.startNew.wp_proof
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
    Cluster.startNew.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end kvreconf
end EtcdGrove
end Perennial
