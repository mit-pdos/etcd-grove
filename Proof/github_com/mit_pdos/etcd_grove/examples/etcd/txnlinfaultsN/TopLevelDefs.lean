/- Lean-first (no Rocq counterpart).

# `etcd/txnlinfaultsN`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.PkgTable
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

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The program: the package's initialization, then `Main(k, clients, ops, sched)` with the schedule
built as a slice literal. -/
def txnlinfaultsNProgram [GoSemanticsFunctions] (k : Nat) (clients ops : w64)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.initialize' #() ;;
  App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Main))
    (Val #(W64 (k : Int)))) (Val #clients)) (Val #ops)) (schedLit steps)

/-- The read package's two metric names (partition's). -/
def txnlinfaultsNNames : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

end adequacy
end EtcdGrove
end Perennial

end

end
