/-
The SwiftPaxos kit's deployment (notes/dsv-swiftpaxos.md; dsv-epaxos's `TopLevelDefs.lean` is the
pattern): its thirteen machines' boot programs (`system`), the machines' heaps (`heapAt`), and the
libraries' representation choice at the start's net protocol names (`libsAt`): the definitions
its top-level statement names. The addresses and listeners are `Start.lean`'s (`swAddrs`,
`swLas`).
-/
module

public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.orch.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client0.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.client5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server1.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server2.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server3.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server4.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server5.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server6.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Start

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Net Dsv

namespace github_com.imdea_software.swiftpaxos.examples.swiftnet

open github_com.imdea_software.swiftpaxos

section system
attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has

/-- The boot program of a command: run its package's initializer `init`, then call its `main`. -/
def boot [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The system: the thirteen machines, from the local states `σ i`: the orchestrator, client
machines 0..5, server machines 1..6 (server 1 the master, 2..6 the replicas; each a command of
`examples/swiftnet/cmd`). -/
def system [GoGlobalContext] (σ : Nat → state) : List (Expr × state) :=
  [(boot cmd.orch.initialize' cmd.orch.main, σ 0),
   (boot cmd.client0.initialize' cmd.client0.main, σ 1),
   (boot cmd.client1.initialize' cmd.client1.main, σ 2),
   (boot cmd.client2.initialize' cmd.client2.main, σ 3),
   (boot cmd.client3.initialize' cmd.client3.main, σ 4),
   (boot cmd.client4.initialize' cmd.client4.main, σ 5),
   (boot cmd.client5.initialize' cmd.client5.main, σ 6),
   (boot cmd.server1.initialize' cmd.server1.main, σ 7),
   (boot cmd.server2.initialize' cmd.server2.main, σ 8),
   (boot cmd.server3.initialize' cmd.server3.main, σ 9),
   (boot cmd.server4.initialize' cmd.server4.main, σ 10),
   (boot cmd.server5.initialize' cmd.server5.main, σ 11),
   (boot cmd.server6.initialize' cmd.server6.main, σ 12)]

/-- A machine's heap over `netDistGF` at the deployment's Go local context `lctx`: the global
ghost state `G` and the local `L`, its local context `lctx` (dsv-epaxos's). -/
abbrev heapAt [lctx : GoLocalContext] (G : GooseGlobalGS HasLC.hasLC netDistGF)
    (L : GooseLocalGS netDistGF) : HeapGS HasLC.hasLC netDistGF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

/-- The libraries' representation choice `l` (a premise of the statement) at the start's net
protocol names `π` (which `SwiftLibs` extends): `l`'s fields with `π` in place of its own. -/
def libsAt (l : SwiftNetPkgState netDistGF) (π : NetProtoGS) : SwiftNetPkgState netDistGF :=
  { toSwiftLibs := { l.toSwiftLibs with toNetProtoGS := π } }

end system

end github_com.imdea_software.swiftpaxos.examples.swiftnet
end Perennial
