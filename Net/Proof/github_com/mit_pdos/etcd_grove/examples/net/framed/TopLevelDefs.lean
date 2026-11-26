/- Lean-first (no Rocq counterpart).

# `net/framed`: the definitions its top-level statement is written in

The program the example's top-level theorem is about (`system`: each node's boot program), which
its statement (`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/framed/TopLevelRobustness.lean`)
names. It imports only the commands' generated translations
(`Net/GeneratedProof/github_com/mit_pdos/etcd_grove/examples/net/framed/cmd/`), no proof (CLAUDE.md,
"Import tiers").
-/
module

public import GooseLang.Ext.Net.Adequacy
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.client
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.junk
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.framed.cmd.server
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.framed

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

/-- A command's program: run its package's initializer `init`, then call its `main` (as goose
calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The server node's program, `cmd/server`'s. -/
abbrev boot_server [GoGlobalContext] : Expr := boot cmd.server.initialize' cmd.server.main

/-- The client node's program, `cmd/client`'s. -/
abbrev boot_client [GoGlobalContext] : Expr := boot cmd.client.initialize' cmd.client.main

/-- The junk node's program, `cmd/junk`'s. -/
abbrev boot_junk [GoGlobalContext] : Expr := boot cmd.junk.initialize' cmd.junk.main

/-- The system: the server, the client and the junk sender, each its own process, from the local
states `σs`, `σc` and `σj`. -/
def system [GoGlobalContext] (σs σc σj : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc), (boot_junk, σj)]

end github_com.mit_pdos.etcd_grove.examples.net.framed
end Perennial

end

end
