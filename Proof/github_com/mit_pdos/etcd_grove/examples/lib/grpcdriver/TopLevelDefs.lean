/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the definitions its top-level statement is written in

gRPC's driver (`examples/lib/grpcdriver`, notes/library-drivers.md): its two machines' boot programs
(the commands `cmd/server` and `cmd/client`), the deployment's address and the bounds, the
definitions the statement (`Spec/.../grpcdriver/TopLevelRobustness.lean`) names.
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client.Base
public import Net.Statement.DistDeploy
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`
(as goose calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The server machine's program: the command `cmd/server` (`Server`: the driver's service served
with gRPC at `Addr`). -/
abbrev boot_server [GoGlobalContext] : Expr := boot cmd.server.initialize' cmd.server.main

/-- The client machine's program: the command `cmd/client` (`Client`: random calls and streams on
one `ClientConn`, each outcome checked, then `Close` and one call after it). -/
abbrev boot_client [GoGlobalContext] : Expr := boot cmd.client.initialize' cmd.client.main

/-- The system: the server and the client, each its own machine, from the local states `σs`
and `σc`. -/
def system [GoGlobalContext] (σs σc : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc)]

/-- The deployment's address: the server's (`grpcdriver.go`'s constant `Addr`). -/
def grpcAddrs : List GoString := [go!"127.0.0.1:7301"]

/-- The statement's thread bound, `2 ^ 31`: every machine keeps fewer than `2 ^ 31` live threads
(`Robust`'s `threads`). The client's `sync.WaitGroup` (its `int32` counter: Perennial's wait-group
specs take `threadBound GF ≤ 2 ^ 31`) needs it. The bridge (`robust_of_distBootIT`, over Perennial's
`goose_dist_adequacy_below`) gives each machine `threadBound GF = grpcThreads`. -/
def grpcThreads : Nat := 2 ^ 31

/-- The statement's step bound, `2 ^ 63 - 1`: executions of fewer than `2 ^ 63 - 1` steps (the
bridge runs an execution of `n` steps at `n + 1` receipts). The client's call ids (`counter`, a
`uint64` from a random start) stay distinct below `2 ^ 64` calls; `2 ^ 63 - 1` is the highest bound
`goose_dist_adequacy_below` takes, as the other drivers'. -/
def grpcSteps : Nat := 2 ^ 63 - 1

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
