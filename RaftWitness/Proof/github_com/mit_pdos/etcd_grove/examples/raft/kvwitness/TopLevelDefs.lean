/- Lean-first (no Rocq counterpart).

# `raft/kvwitness`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.runtime.Threads
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.Init
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.Main
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.MainWitness

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The store's program: the package's initialization, then `Main()`. -/
def kvProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.Main) #()

/-- The store's program with a witness: the package's initialization, then `MainWitness()`. -/
def kvProgramWitness [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.MainWitness) #()

end adequacy
end EtcdGrove
end Perennial

end

end
