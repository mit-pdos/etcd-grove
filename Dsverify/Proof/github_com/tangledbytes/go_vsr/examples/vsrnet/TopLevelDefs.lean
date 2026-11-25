/-
The vr kit's top-level definitions (notes/dsv-vr.md), as paxos's: a command's boot program, the
system of the twelve machines (the orchestrator, client machines 0..5, servers 1..5, each a command
of `examples/vsrnet/cmd`), the deployment's addresses, and a machine's heap (`heapAt`).
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.orch.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client0.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client1.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client2.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client3.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client4.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.client5.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server1.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server2.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server3.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server4.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.cmd.server5.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.Addrs
public import Net.Statement.DistDeploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Shared

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`. -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The system: the twelve machines, from the local states `σ i`: the orchestrator, client
machines 0..5, servers 1..5 (each a command of `examples/vsrnet/cmd`). -/
def system [GoGlobalContext] (σ : Nat → state) : List (Expr × state) :=
  [(boot cmd.orch.initialize' cmd.orch.main, σ 0), (boot cmd.client0.initialize' cmd.client0.main, σ 1), (boot cmd.client1.initialize' cmd.client1.main, σ 2), (boot cmd.client2.initialize' cmd.client2.main, σ 3), (boot cmd.client3.initialize' cmd.client3.main, σ 4), (boot cmd.client4.initialize' cmd.client4.main, σ 5), (boot cmd.client5.initialize' cmd.client5.main, σ 6), (boot cmd.server1.initialize' cmd.server1.main, σ 7), (boot cmd.server2.initialize' cmd.server2.main, σ 8), (boot cmd.server3.initialize' cmd.server3.main, σ 9), (boot cmd.server4.initialize' cmd.server4.main, σ 10), (boot cmd.server5.initialize' cmd.server5.main, σ 11)]

/-- The deployment's addresses: go-vsr's (`Addrs()`), the configuration's (`CfgAddrs()`) and the
client machines' (`ClientAddrs()`). -/
def vrKitAddrs : List GoString := VsrWire.addrs ++ cfgAddrs ++ clientAddrs

/-- A machine's heap over `remoteGF` at the deployment's Go local context `lctx` (the heaps the
proof makes, one per machine): the global ghost state `G` and the local `L`, its local context
`lctx`. The statement's premises hold of every such heap. -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC remoteGF)
    (L : GooseLocalGS remoteGF) : HeapGS HasLC.hasLC remoteGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
