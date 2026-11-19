-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/TopLevelDefs.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# `raft/kvdurable`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.PkgTable
public import Proof.runtime.Threads
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Main
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.MainN

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] durableExts durableExtsSemantics durableExtsInterp durableExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The store's program, its replicas' files in `dir`: the package's initialization, then
`Main(dir)`. -/
def kvdurableProgram [GoSemanticsFunctions] (dir : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Main) #dir

/-- The store's program on `k` voters, its replicas' files in `dir`: the package's initialization,
then `MainN(dir, k)`. -/
def kvdurableProgramN [GoSemanticsFunctions] (dir : GoString) (k : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.MainN) #dir #(W64 (k : Int))

end adequacy
end EtcdGrove
end Perennial

end

end
