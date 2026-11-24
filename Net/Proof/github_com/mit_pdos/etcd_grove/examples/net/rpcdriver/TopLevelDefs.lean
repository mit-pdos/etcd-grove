/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the definitions its top-level statement is written in

net/rpc's driver (`examples/net/rpcdriver`, notes/library-drivers.md): its two machines' boot
programs (the commands `cmd/server` and `cmd/client`), the deployment's addresses and the step
bound, the definitions the statement (`Spec/.../rpcdriver/TopLevelRobustness.lean`) names.
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client.Base
public import Net.Statement.DistDeploy
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`
(as goose calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The server machine's program: the command `cmd/server` (`Register`, then `Server`: net/rpc
over raw TCP at `TCPAddr` and over HTTP at `HTTPAddr`). -/
abbrev boot_server [GoGlobalContext] : Expr := boot cmd.server.initialize' cmd.server.main

/-- The client machine's program: the command `cmd/client` (`Register`, then `Client`: random
calls, each outcome checked). -/
abbrev boot_client [GoGlobalContext] : Expr := boot cmd.client.initialize' cmd.client.main

/-- The system: the server and the client, each its own machine, from the local states `σs`
and `σc`. -/
def system [GoGlobalContext] (σs σc : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc)]

/-- The deployment's addresses: the server's two (`rpcdriver.go`'s constants `TCPAddr` and
`HTTPAddr`). -/
def rpcAddrs : List GoString := [go!"127.0.0.1:7211", go!"127.0.0.1:7212"]

/-- The statement's step bound, `2 ^ 31 - 1`: Net's net/rpc server (`Server.ServeCodec.spec`, run
by `rpc.Accept` and by the HTTP handler `rpc.HandleHTTP` registers) needs the machine's thread bound
`threadBound GF ≤ 2 ^ 31` (its wait group's counter is an `int32`), and the deployment bridge bounds
the threads by the step count (as the net/rpc kits, `swiftnet`'s and `epaxosnet`'s statements). -/
def rpcStepBound : Nat := 2 ^ 31 - 1

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
