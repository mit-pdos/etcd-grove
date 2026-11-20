/- Lean-first (no Rocq counterpart).

# `k8s/all`: the definitions its top-level statement is written in

The program the one closed Kubernetes theorem (`k8s_safe`, `notes/k8s-unified-scope.md`) is about, and
the other definitions its statement names: the ghost-state bundle (the k8s etcd3 driver's, with
iris-lean's non-atomic invariants for porcupine), the read package's metric names, and the two
clusters' addresses and data directories, the store's (`k8s_etcd3N`, `k` members) then the
compactor's (`k8s_compactor.clusterCfg`, three members).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Cluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.SchedLit
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

/-- The functors: putget's (the universal camera `AllG` at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state), and iris-lean's non-atomic invariants at slot 11
(porcupine's). Every other slot is the unit functor. -/
def k8sGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses are stated over every
instance of the ghost state whose Go local context is the semantics' own). -/
abbrev k8sHeapAt (hG : HeapGS .hasLC k8sGF) (lctx : GoLocalContext) : HeapGS .hasLC k8sGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

end EtcdGrove
end Perennial

end

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **The program**: `k8sall`'s initialization, then `Main(k, clients, ops, watchers, wops, sched1,
sched2)` with the two schedules `steps₁` (the store's cluster) and `steps₂` (the compactor's) built as
slice literals (`schedLit`). -/
def k8sProgram [GoSemanticsFunctions] (k : Nat) (clients ops watchers wops : w64)
    (steps₁ steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.all.initialize' #() ;;
  App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.Main))
    (Val #(W64 (k : Int)))) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops))
    (schedLit steps₁)) (schedLit steps₂)

/-- The read package's two metric names, which the program's initialization registers (`readRegPerm`,
D16). -/
def k8sNames : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- The compactor cluster's addresses: its three members' peer addresses, their client addresses and
their bridges' addresses (`k8s_compactor.clusterCfg`'s). -/
def k8sCompactorAddrs : List GoString :=
  [k8s_compactor.clusterCfg.Peer1', k8s_compactor.clusterCfg.Peer2', k8s_compactor.clusterCfg.Peer3',
    k8s_compactor.clusterCfg.Client1', k8s_compactor.clusterCfg.Client2',
    k8s_compactor.clusterCfg.Client3',
    k8s_compactor.clusterCfg.Bridge1', k8s_compactor.clusterCfg.Bridge2',
    k8s_compactor.clusterCfg.Bridge3']

/-- The compactor cluster's members' data directories `<name>.etcd`. -/
def k8sCompactorDirs : List GoString :=
  [(memberDataDir k8s_compactor.clusterCfg.Name1'),
    (memberDataDir k8s_compactor.clusterCfg.Name2'),
    (memberDataDir k8s_compactor.clusterCfg.Name3')]

/-- **The program's addresses**: the store cluster's (`k8s_etcd3N.k8setcd3NAddrs k`: its `k` members'
peer and client addresses and its bridges'), then the compactor cluster's. -/
def k8sAddrs (k : Nat) : List GoString := k8s_etcd3N.k8setcd3NAddrs k ++ k8sCompactorAddrs

/-- **The program's data directories**: the store cluster's `k8setcd3N-i.etcd`, then the compactor
cluster's `k8scompactorp-{1,2,3}.etcd`. -/
def k8sDirs (k : Nat) : List GoString := k8s_etcd3N.k8setcd3NDirs k ++ k8sCompactorDirs

end adequacy
end EtcdGrove
end Perennial

end

end
