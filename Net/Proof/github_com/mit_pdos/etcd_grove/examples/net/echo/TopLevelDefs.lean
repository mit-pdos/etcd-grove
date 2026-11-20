/- Lean-first (no Rocq counterpart).

# `net/echo`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.junk.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.junk.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server.PkgTable
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The boot program of a command: run its package's initializer `init`, then call its `main`
(as goose calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The server node's program: the command `cmd/server`. -/
abbrev boot_server [GoGlobalContext] : Expr := boot cmd.server.initialize' cmd.server.main

/-- The client node's program: the command `cmd/client`. -/
abbrev boot_client [GoGlobalContext] : Expr := boot cmd.client.initialize' cmd.client.main

/-- The junk node's program: the command `cmd/junk`. -/
abbrev boot_junk [GoGlobalContext] : Expr := boot cmd.junk.initialize' cmd.junk.main

/-- The system: the server, the client and the junk sender, each its own process, from the
local states `σs`, `σc` and `σj`. -/
def system [GoGlobalContext] (σs σc σj : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc), (boot_junk, σj)]

end github_com.mit_pdos.etcd_grove.examples.net.echo
end Perennial

end

end
