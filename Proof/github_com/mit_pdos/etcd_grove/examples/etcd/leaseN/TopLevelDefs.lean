/- Lean-first (no Rocq counterpart).

# `etcd/leaseN`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.PkgTable
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

/-- The program: `leaseN`'s initialization, then `Main(k)`. -/
def leaseNProgram [GoSemanticsFunctions] (k : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Main) #(W64 (k : Int))

/-- The metric names the program's initialization registers (its closure's `PRE_RES` packages', D16;
mustreg, 2026-11-20, until then the read package's two, `readRegPerm`): its `initNames`. -/
def leaseNNames : List GoString := _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.initNames

end adequacy
end EtcdGrove
end Perennial

end

end
