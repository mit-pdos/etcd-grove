/-
**remote's counter instance, closed** (`notes/remote-port-plan.md`, R4): four machines, none of
which crashes — the orchestrator (`remote.Check` of two clients' increments and reads against the
counter's model with pending increments), two client nodes (each `remote.ServeClient`, its operation
a `remote.Do` at the server) and the server (lintest/counter's `Counter`, `remote.Serve`d) —
deployed at `counterAddrs` (`DistDeploy`: the addresses distinct and valid, no connection, no
listener). In every execution of fewer than `2^63` steps, with any number of threads, no thread of
any machine is stuck and none has a top-level panic (`Robust`, `Robustness/Statement.lean`). Since
the orchestrator panics unless porcupine accepts the history, this says porcupine accepts every
history, under every fault the net extension allows (connections cut at any byte, timeouts,
abandoned dials), with increments of unknown outcome. Proved in
`Net/Proof/.../lib/remote/counter/TopLevelRobustness.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- See the file header. -/
def counter_remote_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions] [c0_sem : cmd.client0.Assumptions]
    [c1_sem : cmd.client1.Assumptions] [srv_sem : cmd.server.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σo σ0 σ1 σs : state) (g : GlobalState) (threads : Nat),
    DistDeploy counterAddrs (system σo σ0 σ1 σs) g →
    Robustness.Robust [] (system σo σ0 σ1 σs) g threads (2 ^ 63)

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
