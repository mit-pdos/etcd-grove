/- Lean-first (no Rocq counterpart).

# `goose/prophkv`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Code.github_com.mit_pdos.etcd_grove.examples.goose.prophkv
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace goose_prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open github_com.mit_pdos.etcd_grove.examples.goose.prophkv

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section program

variable [go_gctx : GoGlobalContext]

/-- The program: initialize the package, then call `Main` (as goose calls a function), which runs
`Test` and panics unless its answer is `"a"` or `"b"`. -/
def prog : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Main []))) (Val #())) (Val #()))

end program
end goose_prophkv
end EtcdGrove
end Perennial

end

end
