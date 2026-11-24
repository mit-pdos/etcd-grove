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
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- **`Main`'s files, by name** (`FilePaths(MainConfig("mvccfull"))`): the members' `mvccfull-0.db`,
`mvccfull-1.db` and the builders' `mvccfull-b<n>.db`. -/
def mvccfullNames [GooseExts] [GoGlobalContext] : List GoString :=
  filePathsM (mainConfigM go!"mvccfull" (zeroValDef : Mix))

end mvccfull
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

/-- The program: `mvccfull`'s initialization, then `Run(MainConfig(r/mvccfull))`: `Main`'s run with
its files in the directory `r`, its report dropped, as `Main` does (S3e; until then `Main()`, whose prefix `mvccfull` is relative). -/
def mvccfullProgram [GoSemanticsFunctions] (r : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.mvccfull.initialize' #() ;;
  ((@! github_com.mit_pdos.etcd_grove.examples.mvccfull.Run)
    ((@! github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig) #(Fs.child r go!"mvccfull")) ;; #())

end adequacy
end EtcdGrove
end Perennial

end

end
