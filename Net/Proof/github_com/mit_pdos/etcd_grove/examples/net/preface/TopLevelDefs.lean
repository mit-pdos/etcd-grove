/- Lean-first (no Rocq counterpart).

# `net/preface`: the definitions its top-level statement is written in

The program the example's top-level theorem is about (`system`: each node's boot program), which
its statement (`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/preface/TopLevelRobustness.lean`)
names. It imports only the commands' generated translations
(`Net/GeneratedProof/github_com/mit_pdos/etcd_grove/examples/net/preface/cmd/`), no proof (CLAUDE.md,
"Import tiers").
-/
module

public import GooseLang.Ext.Net.Adequacy
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.client
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.junk
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

/-- The program of a command whose package's initializer is `init` and whose `main` is `main`:
initialize the command's package (and so its imports), then call its `main` (as goose calls a
function: resolve it, then apply it). -/
def bootOf [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The program of the server's command `cmd/server`. -/
abbrev boot_server [GoGlobalContext] : Expr := bootOf cmd.server.initialize' cmd.server.main

/-- The program of the client's command `cmd/client`. -/
abbrev boot_client [GoGlobalContext] : Expr := bootOf cmd.client.initialize' cmd.client.main

/-- The program of the junk sender's command `cmd/junk`. -/
abbrev boot_junk [GoGlobalContext] : Expr := bootOf cmd.junk.initialize' cmd.junk.main

/-- The system: the server, the client and the junk sender, each running its command's program,
from the local states `σs`, `σc` and `σj`. -/
def system [GoGlobalContext] (σs σc σj : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc), (boot_junk, σj)]

end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial

end

end
