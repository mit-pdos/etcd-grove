/- Lean-first (no Rocq counterpart).

# `net/acceptloop`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server.PkgTable
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The server node's program: initialize the `server` command's package, then call its `main`
(as goose calls a function: resolve it, then apply it). -/
def boot_server [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.server.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.server.main []))) (Val #())) (Val #()))

/-- The client node's program: the same for the `client` command. -/
def boot_client [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.client.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.client.main []))) (Val #())) (Val #()))

/-- The system: the server and the client commands, each a process, from the local states `σs`
and `σc`. -/
def system [GoGlobalContext] (σs σc : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc)]

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial

end

end
