/- Lean-first (no Rocq counterpart).

# `osfs/crashlog`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import GooseLang.Ext.Fs.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.Boot
public import Proof.os.Crash
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.crashlog

open Fs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

/-- The boot program: initialize the package, then call `Boot(dir)`. -/
def boot [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Boot []))) (Val #())) (Val #dir))

end osfs_crashlog
end EtcdGrove
end Perennial

end

end
