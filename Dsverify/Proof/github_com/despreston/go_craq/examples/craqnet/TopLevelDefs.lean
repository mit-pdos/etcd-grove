/-
The craq kit's deployment (notes/dsv-craq.md): its twelve machines' boot programs and addresses,
the definitions its top-level statement (`Spec/github_com/despreston/go_craq/examples/craqnet/TopLevelRobustness.lean`)
names (as paxos's `TopLevelDefs.lean`).
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.orch.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client0.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client1.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client2.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client3.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.client4.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server1.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server2.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server3.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server4.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server5.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.cmd.server6.Base
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Kit

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.despreston.go_craq.examples.craqnet

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`. -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The system: the twelve machines, from the local states `σ i`: the orchestrator, client
machines 0..4, server machines 1..6 (each a command of `examples/craqnet/cmd`). -/
def system [GoGlobalContext] (σ : Nat → state) : List (Expr × state) :=
  [(boot cmd.orch.initialize' cmd.orch.main, σ 0), (boot cmd.client0.initialize' cmd.client0.main, σ 1), (boot cmd.client1.initialize' cmd.client1.main, σ 2), (boot cmd.client2.initialize' cmd.client2.main, σ 3), (boot cmd.client3.initialize' cmd.client3.main, σ 4), (boot cmd.client4.initialize' cmd.client4.main, σ 5), (boot cmd.server1.initialize' cmd.server1.main, σ 6), (boot cmd.server2.initialize' cmd.server2.main, σ 7), (boot cmd.server3.initialize' cmd.server3.main, σ 8), (boot cmd.server4.initialize' cmd.server4.main, σ 9), (boot cmd.server5.initialize' cmd.server5.main, σ 10), (boot cmd.server6.initialize' cmd.server6.main, σ 11)]

/-- The deployment's addresses: the server machines' net/rpc addresses (`ServerAddrs()`), the
client machines' (`ClientAddrs()`), the configuration addresses (`ConfAddrs()`). -/
def craqKitAddrs : List GoString := serverAddrs ++ clientAddrs ++ confAddrs

end github_com.despreston.go_craq.examples.craqnet
end Perennial
