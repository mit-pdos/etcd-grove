/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkv`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, in a defs module so that the statement (`Spec/.../TopLevelRobustness.lean`) imports no
proof (CLAUDE.md, "Import tiers").
-/
module

public import Robustness.NoExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkv.PkgTable
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.StepBound
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace logkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] Robustness.noExts Robustness.noExtsSemantics Robustness.noExtsInterp

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The register's program: the package's initialization, then `Main()`. -/
def logkvProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkv.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkv.Main) #()

end adequacy
end logkv
end lintest
end EtcdGrove
end Perennial

end

end
