/- Lean-first (no Rocq counterpart).

# `mvccfull`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.PkgTable
public import Proof.runtime.StartFiles
public import Proof.runtime.Threads

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end EtcdGrove
end Perennial

end

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The program: `mvccfull`'s initialization, then `MainAt(r)`: `Main`'s run with its files in the
directory `r` (`Run(MainConfig(r/mvccfull))`), after the program's own checks that `r` fits and that
nothing is at any of the run's file paths (P3 of the pure-premise plan, 2026-11-24; S3e to then:
`Run(MainConfig(r/mvccfull))`, those two facts premises of the statement; until S3e `Main()`, whose
prefix `mvccfull` is relative). -/
def mvccfullProgram [GoSemanticsFunctions] (r : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.mvccfull.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.MainAt) #r

end adequacy
end EtcdGrove
end Perennial

end

end
