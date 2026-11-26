/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the definitions its top-level statement is written in

net/http's driver (`examples/net/httpdriver`, notes/library-drivers.md): its two machines' boot
programs (the commands `cmd/server` and `cmd/client`), the deployment's address and the two bounds,
the definitions the statement (`Spec/.../httpdriver/TopLevelRobustness.lean`) names.
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client.Base
public import Net.Statement.DistDeploy
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`
(as goose calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The server machine's program: the command `cmd/server` (`Server`: a `ServeMux` with the
handlers `/echo` and `/status`, served with `http.Serve` at `Addr`). -/
abbrev boot_server [GoGlobalContext] : Expr := boot cmd.server.initialize' cmd.server.main

/-- The client machine's program: the command `cmd/client` (`Client`: random requests on random
connections, each response read with `http.ReadResponse` and checked). -/
abbrev boot_client [GoGlobalContext] : Expr := boot cmd.client.initialize' cmd.client.main

/-- The system: the server and the client, each its own machine, from the local states `σs`
and `σc`. -/
def system [GoGlobalContext] (σs σc : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc)]

/-- The deployment's address: the server's (`httpdriver.go`'s constant `Addr`). -/
def httpAddrs : List GoString := [go!"127.0.0.1:7401"]

/-- The statement's thread bound, `2 ^ 30`: every machine keeps fewer than `2 ^ 30` live threads
(`Robust`'s `threads`). net/http's first initialization needs it (`net.http.wp_init_first`'s
`threadBound GF ≤ 2 ^ 30`: the `RWMutex` of a `ServeMux`, whose reader-slot pools hold at most
`2 ^ 30` readers). The bridge (`robust_of_distBootIT`, over Perennial's `goose_dist_adequacy_below`)
gives each machine `threadBound GF = httpThreads`. -/
def httpThreads : Nat := 2 ^ 30

/-- The statement's step bound, `2 ^ 63 - 1`: executions of fewer than `2 ^ 63 - 1` steps (the
bridge runs an execution of `n` steps at `n + 1` receipts). No spec the proof uses bounds the receipts
below `2 ^ 64`; the value follows `rpcdriver`'s `rpcSteps` and the dsverify kits' `2 ^ 63`. -/
def httpSteps : Nat := 2 ^ 63 - 1

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
