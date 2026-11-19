/- Lean-first (no Rocq counterpart).

# `k8s/etcd3`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.SchedLit
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

/-- The functors: putget's (`putgetGF`: the universal camera `AllG` at slot 0, then invariants,
later credits, GooseLang's heap, prophecies and package state), and
iris-lean's non-atomic invariants at slot 11 (as the counter's `counterGF`). Every other slot is
the unit functor. -/
def k8setcd3GF : BundledGFunctors := fun i =>
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

/-- **A ghost-state instance at the local context `lctx`** (as putget's `heapAt`). -/
abbrev k8setcd3HeapAt (hG : HeapGS .hasLC k8setcd3GF) (lctx : GoLocalContext) : HeapGS .hasLC k8setcd3GF :=
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

/-- The program: `k8setcd3`'s initialization, then `Main(clients, ops, watchers, wops)`. -/
def k8setcd3Program [GoSemanticsFunctions] (clients ops watchers wops : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Main) #clients #ops #watchers #wops

/-- The read package's two metric names, which `k8setcd3`'s initialization registers (`readRegPerm`,
D16). -/
def k8setcd3Names : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- The program with `k` members: `k8setcd3`'s initialization, then
`MainCluster(k, clients, ops, watchers, wops)`. -/
def k8setcd3CProgram [GoSemanticsFunctions] (k : Nat) (clients ops watchers wops : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialize' #() ;;
  App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainCluster))
    (Val #(W64 (k : Int)))) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)

/-- The program with `k` members under a partition schedule: `k8setcd3`'s initialization, then
`MainPartition(k, clients, ops, watchers, wops, sched)` with the schedule `steps` built as a slice
literal (`schedLit`, as the k8s compactor's `k8scompactorPProgram`). -/
def k8setcd3PProgram [GoSemanticsFunctions] (k : Nat) (clients ops watchers wops : w64)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialize' #() ;;
  App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition))
    (Val #(W64 (k : Int)))) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)) (schedLit steps)

end adequacy
end EtcdGrove
end Perennial

end

end
