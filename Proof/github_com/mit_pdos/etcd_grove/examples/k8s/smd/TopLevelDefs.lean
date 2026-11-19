/- Lean-first (no Rocq counterpart).

# `k8s/smd`: the definitions its top-level statement is written in

The program the structured-merge-diff driver's top-level theorem is about, in its own module so
that the statement (`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import
tiers").
-/
module

public import Code.github_com.mit_pdos.etcd_grove.examples.k8s.smd
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section program

variable [go_gctx : GoGlobalContext]

/-- The program: initialize the driver's package (which initializes structured-merge-diff's
packages and the standard library's they import), then call `Main` (as goose calls a function),
which runs the nine checked apply/update steps and panics on any unexpected result. -/
def smdProgram : Expr :=
  Seq (App (Val github_com.mit_pdos.etcd_grove.examples.k8s.smd.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve github_com.mit_pdos.etcd_grove.examples.k8s.smd.Main []))) (Val #())) (Val #()))

end program
end k8s_smd
end EtcdGrove
end Perennial

end

end
