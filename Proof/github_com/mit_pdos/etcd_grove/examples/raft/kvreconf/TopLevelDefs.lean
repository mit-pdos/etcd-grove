/- Lean-first (no Rocq counterpart).

# `raft/kvreconf`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.PkgTable
public import Proof.runtime.Threads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.MainN

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The store's program: the package's initialization, then `Main()`. -/
def kvreconfProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Main) #()

/-- The store's program on `k` voters: the package's initialization, then `MainN(k)`. -/
def kvreconfProgramN [GoSemanticsFunctions] (k : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.MainN) #(W64 (k : Int))

end adequacy
end EtcdGrove
end Perennial

end

end
