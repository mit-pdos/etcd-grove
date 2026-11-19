/- Lean-first (no Rocq counterpart).

# `k8s/compactor`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Cluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.PkgTable
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

/-- The functors (as the register's `registerGF`): the universal camera (`AllG`) at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def k8scompactorGF : BundledGFunctors := fun i =>
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
  | _ => ⟨constOF Unit, inferInstance⟩

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses below are stated over
every instance of the ghost state whose Go local context is the semantics' own). -/
abbrev heapAtKc (hG : HeapGS .hasLC k8scompactorGF) (lctx : GoLocalContext) : HeapGS .hasLC k8scompactorGF :=
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

/-- The program: the compactor example's initialization, then `Main()`. -/
def k8scompactorProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.compactor.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main) #()

/-- The read package's two metric names, which the example's initialization registers
(`readRegPerm`, D16). -/
def k8scompactorNames : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- The program with three members: the compactor example's initialization, then
`MainPartition(sched)` with the schedule built as a slice literal. -/
def k8scompactorPProgram [GoSemanticsFunctions]
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.compactor.initialize' #() ;;
  App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition)) (schedLit steps)

/-- The program's addresses: the three members' peer addresses, their client addresses, and the
bridges' addresses (`clusterCfg`'s). -/
def k8scompactorPAddrs : List GoString :=
  [k8s_compactor.clusterCfg.Peer1', k8s_compactor.clusterCfg.Peer2', k8s_compactor.clusterCfg.Peer3',
    k8s_compactor.clusterCfg.Client1', k8s_compactor.clusterCfg.Client2',
    k8s_compactor.clusterCfg.Client3',
    k8s_compactor.clusterCfg.Bridge1', k8s_compactor.clusterCfg.Bridge2',
    k8s_compactor.clusterCfg.Bridge3']

/-- The members' data directories `<name>.etcd` (sweep repairs 1, W3/W4: until then their WAL directories). -/
def k8scompactorPDataDirs : List GoString :=
  [(k8s_compactor.clusterCfg.Name1' ++ go!".etcd"),
    (k8s_compactor.clusterCfg.Name2' ++ go!".etcd"),
    (k8s_compactor.clusterCfg.Name3' ++ go!".etcd")]

end adequacy
end EtcdGrove
end Perennial

end

end
