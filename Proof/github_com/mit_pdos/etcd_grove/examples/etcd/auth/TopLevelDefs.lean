/- Lean-first (no Rocq counterpart).

# `etcd/auth`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.PkgTable
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

/-- The program: `authkv`'s initialization, then `Main()`. -/
def authkvProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.auth.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth.Main) #()

/-- The metric names the program's initialization registers (its closure's `PRE_RES` packages', D16;
mustreg, 2026-11-20, until then the read package's two, `readRegPerm`): its `initNames`. -/
def authkvNames : List GoString := _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.etcd.auth.initNames

end adequacy
end EtcdGrove
end Perennial

end

end
