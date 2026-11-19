/- Lean-first (no Rocq counterpart).

# `net/duplex`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import GooseLang.Ext.Tcp.Adequacy
public import GooseLang.Ext.Tcp.Deploy
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client.PkgTable
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.PkgTable
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The server node's program, the command `cmd/server`: its package initialization, then its
`main` (as goose calls a function: resolve it, then apply it). -/
def boot_server [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.server.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.server.main []))) (Val #())) (Val #()))

/-- The client node's program, the command `cmd/client`. -/
def boot_client [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.client.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.client.main []))) (Val #())) (Val #()))

/-- The system: the server and the client, each its own process, from the local states `σs` and
`σc`. -/
def system [GoGlobalContext] (σs σc : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc)]

end github_com.mit_pdos.etcd_grove.examples.net.duplex
end Perennial

end

end
