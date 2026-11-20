/- Lean-first (no Rocq counterpart).

# `net/shutdown`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node.PkgTable
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

open github_com.mit_pdos.etcd_grove.examples.net.wire (addrInv)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The program of the node's command `cmd/node`: initialize the command's package (and so its
imports), then call its `main` (as goose calls a function: resolve it, then apply it). -/
def boot_node [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.node.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.node.main []))) (Val #())) (Val #()))

/-- The system: the one node, running its command's program, from the local state `σ`. -/
def system [GoGlobalContext] (σ : state) : List (Expr × state) :=
  [(boot_node, σ)]

end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

end

end
