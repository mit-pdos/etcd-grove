/- Lean-first (no Rocq counterpart).

# `etcd/cache`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Code.github_com.mit_pdos.etcd_grove.examples.etcd.cache
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Init
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

/-- The program: `cachekv`'s initialization, then `Main(nw, nops)`. -/
def cachekvProgram [GoSemanticsFunctions] (nw nops : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.cache.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.etcd.cache.Main) #nw #nops

/-- The metric names the program's initialization registers (its closure's `PRE_RES` packages', D16;
mustreg, 2026-11-20, until then the read package's two, `readRegPerm`): its `initNames`,
which is `etcdstart`'s (the same registering packages; written so because the root's `Init` is a
linking module, `etc/tier-linking.txt`, which this definitions module may not import). -/
def cachekvNames : List GoString := _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.initNames

end adequacy
end EtcdGrove
end Perennial

end

end
