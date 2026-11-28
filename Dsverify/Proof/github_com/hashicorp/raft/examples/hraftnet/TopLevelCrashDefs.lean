/- Lean-first (no Rocq counterpart).

The hraft kit's crash deployment (`hraft_robust`; notes/dsv-hraft.md, "hraft_robust"): its twelve
machines' boot programs over the net extension and the Linux file extension (`kvraftExts`), the
definitions the statement (`Spec/.../hraftnet/TopLevelRobustness.lean`, `hraft_robust.spec`) names.
Hand-written beside kitgen's `TopLevelDefs.lean` (the no-crash deployment's, over `netExts` alone),
which stays as it is: the servers here are the restartable ones (`cmd/rserver1..6`, package
`rserver`), the orchestrator and the clients the same commands.
-/
module

public import GooseLang.Ext.NetFs.Adequacy
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.orch
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.client0
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.client1
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.client2
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.client3
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.client4
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.rserver1
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.rserver2
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.rserver3
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.rserver4
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.rserver5
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.cmd.rserver6
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI NetFs

namespace github_com.hashicorp.raft.examples.hraftnet

section programs
attribute [local instance] kvraftExts
variable [GoGlobalContext]

/-- The boot program of a command, over `kvraftExts`: run its package's initializer `init`, then
call its `main` (kitgen's `boot`, over the net and file extensions). -/
def bootFs (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The machines that crash: the restartable server machines 1..6 (`cmd/rserver<id>`:
`rserver.ServerR(id, rserver.DataDir)`), from the local states `σ 6`, ..., `σ 11`. -/
def crashServers (σ : Nat → state) : List (Expr × state) :=
  [(bootFs cmd.rserver1.initialize' cmd.rserver1.main, σ 6),
   (bootFs cmd.rserver2.initialize' cmd.rserver2.main, σ 7),
   (bootFs cmd.rserver3.initialize' cmd.rserver3.main, σ 8),
   (bootFs cmd.rserver4.initialize' cmd.rserver4.main, σ 9),
   (bootFs cmd.rserver5.initialize' cmd.rserver5.main, σ 10),
   (bootFs cmd.rserver6.initialize' cmd.rserver6.main, σ 11)]

/-- The machines that never crash: the orchestrator and client machines 0..4 (the no-crash
deployment's commands), from the local states `σ 0`, ..., `σ 5`. -/
def stableMachines (σ : Nat → state) : List (Expr × state) :=
  [(bootFs cmd.orch.initialize' cmd.orch.main, σ 0),
   (bootFs cmd.client0.initialize' cmd.client0.main, σ 1),
   (bootFs cmd.client1.initialize' cmd.client1.main, σ 2),
   (bootFs cmd.client2.initialize' cmd.client2.main, σ 3),
   (bootFs cmd.client3.initialize' cmd.client3.main, σ 4),
   (bootFs cmd.client4.initialize' cmd.client4.main, σ 5)]

end programs

section fs
attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExts_hasFs

/-- A machine's Linux file system: the file extension's local state. -/
abbrev fsOf (σ : state) : Fs.OsState := extLocal Fs.fsExt σ.world

/-- The restartable servers' data directory (`rserver.DataDir`). -/
def hraftDataDir : GoString := go!"/var/lib/hraft"

end fs

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
