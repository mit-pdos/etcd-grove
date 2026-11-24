/-
The gryff kit's deployment (notes/dsv-gryff.md): its eleven machines' boot programs and the addresses
`DistDeploy` lists, the definitions its top-level statement
(`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean`) names. The master and the replicas
listen at wildcards (`":7501"`, `":7502".."7504"`, `":8502".."8504"`), not at listed addresses: only
the client machines' addresses (`ClientAddrs()`) are `DistDeploy`'s.
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.orch.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client0.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client1.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client2.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client3.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client4.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.client5.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server1.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server2.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server3.Base
public import Dsverify.Proof.gryff.examples.gryffnet.cmd.server4.Base
public import Dsverify.Proof.gryff.examples.gryffnet.KitSpecs
public import Net.Statement.DistDeploy
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace gryff.examples.gryffnet

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The boot program of a command: run its package's initializer `init`, then call its `main`. -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The system: the eleven machines, from the local states `σ i`: the orchestrator, client
machines 0..5, server 1 (the master) and servers 2..4 (the replicas), each a command of
`examples/gryffnet/cmd`. -/
def system [GoGlobalContext] (σ : Nat → state) : List (Expr × state) :=
  [(boot cmd.orch.initialize' cmd.orch.main, σ 0), (boot cmd.client0.initialize' cmd.client0.main, σ 1), (boot cmd.client1.initialize' cmd.client1.main, σ 2), (boot cmd.client2.initialize' cmd.client2.main, σ 3), (boot cmd.client3.initialize' cmd.client3.main, σ 4), (boot cmd.client4.initialize' cmd.client4.main, σ 5), (boot cmd.client5.initialize' cmd.client5.main, σ 6), (boot cmd.server1.initialize' cmd.server1.main, σ 7), (boot cmd.server2.initialize' cmd.server2.main, σ 8), (boot cmd.server3.initialize' cmd.server3.main, σ 9), (boot cmd.server4.initialize' cmd.server4.main, σ 10)]

/-- The deployment's listed addresses: the client machines' (`ClientAddrs()`). -/
def gryffKitAddrs : List GoString := clientAddrs

end gryff.examples.gryffnet
end Perennial
