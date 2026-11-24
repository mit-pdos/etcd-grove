/-
The programs and names `counter_remote_robust.spec` (`Net/Spec/.../lib/remote/counter/
TopLevelRobustness.lean`) is stated in: each machine's boot program (its command's initializer,
then its `main`), the system of the four machines, and the deployment's addresses.
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client0.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server.Base
public import Net.Statement.DistDeploy
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`. -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The orchestrator's program: `cmd/orch` (`remote.Check` of two clients). -/
abbrev boot_orch [GoGlobalContext] : Expr := boot cmd.orch.initialize' cmd.orch.main

/-- Client node 0's program: `cmd/client0`. -/
abbrev boot_client0 [GoGlobalContext] : Expr := boot cmd.client0.initialize' cmd.client0.main

/-- Client node 1's program: `cmd/client1`. -/
abbrev boot_client1 [GoGlobalContext] : Expr := boot cmd.client1.initialize' cmd.client1.main

/-- The server's program: `cmd/server` (lintest/counter's `Counter`, served). -/
abbrev boot_server [GoGlobalContext] : Expr := boot cmd.server.initialize' cmd.server.main

/-- The system: the orchestrator, the two client nodes and the server, each its own machine, from
the local states `σo`, `σ0`, `σ1`, `σs`. -/
def system [GoGlobalContext] (σo σ0 σ1 σs : state) : List (Expr × state) :=
  [(boot_orch, σo), (boot_client0, σ0), (boot_client1, σ1), (boot_server, σs)]

/-- The deployment's addresses: client node 0's, client node 1's, the server's (`ClientAddr0`,
`ClientAddr1`, `ServerAddr`). -/
def counterAddrs [GoGlobalContext] : List GoString :=
  [go!"127.0.0.1:7302", go!"127.0.0.1:7303", go!"127.0.0.1:7301"]

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
