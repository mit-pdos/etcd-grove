/-
The QuePaxa kit's deployment (notes/dsv-quepaxa.md): its twelve machines' boot programs and listed
addresses, the definitions its top-level statement (`Spec/raxos/examples/quepaxanet/
TopLevelRobustness.lean`) names.
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.orch.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client0.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client1.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client2.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client3.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client4.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client5.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server1.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server2.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server3.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server4.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server5.Base
public import Dsverify.Proof.raxos.examples.quepaxanet.StartAddr
public import Net.Statement.DistDeploy
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace raxos.examples.quepaxanet

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`. -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The system: the twelve machines, from the local states `σ i`: the orchestrator, client machines
0..5, servers 1..5 (each a command of `examples/quepaxanet/cmd`). -/
def system [GoGlobalContext] (σ : Nat → state) : List (Expr × state) :=
  [(boot cmd.orch.initialize' cmd.orch.main, σ 0), (boot cmd.client0.initialize' cmd.client0.main, σ 1), (boot cmd.client1.initialize' cmd.client1.main, σ 2), (boot cmd.client2.initialize' cmd.client2.main, σ 3), (boot cmd.client3.initialize' cmd.client3.main, σ 4), (boot cmd.client4.initialize' cmd.client4.main, σ 5), (boot cmd.client5.initialize' cmd.client5.main, σ 6), (boot cmd.server1.initialize' cmd.server1.main, σ 7), (boot cmd.server2.initialize' cmd.server2.main, σ 8), (boot cmd.server3.initialize' cmd.server3.main, σ 9), (boot cmd.server4.initialize' cmd.server4.main, σ 10), (boot cmd.server5.initialize' cmd.server5.main, σ 11)]

/-- The deployment's listed addresses (`StartAddr.lean`'s `kitAddrs`): every address a machine
listens at or dials, but the proxies' and the recorders' ports, which the servers listen at as
wildcards (`0.0.0.0:port`, `kitLis`) and the others dial at `127.0.0.1:port`. -/
def quepaxaKitAddrs : List GoString := kitAddrs

end raxos.examples.quepaxanet
end Perennial
