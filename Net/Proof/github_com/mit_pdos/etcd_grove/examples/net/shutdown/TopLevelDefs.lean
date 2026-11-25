/- Lean-first (no Rocq counterpart).

# `net/shutdown`: the definitions its top-level statement is written in

The program the example's top-level theorem is about (`system`: each node's boot program), which
its statement (`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/shutdown/TopLevelRobustness.lean`)
names. It imports only the commands' generated translations
(`Net/GeneratedProof/github_com/mit_pdos/etcd_grove/examples/net/shutdown/cmd/`), no proof (CLAUDE.md,
"Import tiers").
-/
module

public import GooseLang.Ext.Net.Adequacy
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

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
