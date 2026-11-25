/- Lean-first (no Rocq counterpart).

# `net/shutdown`: the top-level robustness result, stated

`shutdown_crash_robust`: the one node, `cmd/node`, at `127.0.0.1:7106` (`examples/net/shutdown/`),
each a machine that may crash and restart, satisfy the generic robustness statement
(`Robustness/Statement.lean`, `Robust`): in every execution of fewer than `bound` steps, no thread
of any machine is stuck and none has an unrecovered panic, so the node's checks (`shutdown.Run`:
every operation after a `Close` fails) never fails. This file only states it (to audit); the proof
is in `Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/shutdown/TopLevelRobustness.lean`.

What it assumes:
* **The extension**: `netExts = [netExt]` (`GooseLang/Ext/Net/Adequacy.lean`), GooseLang with the
  trusted semantics of TCP of `GooseLang/Ext/Net/Impl.lean`; `Robust` starts every machine with no
  listener and the network with no connection (its `initLocal`/`initGlobal`, D26).
* **The deployment** (`Impl.lean`, D13): a closed world, stated in prose only (no process outside the
  deployment accepts a connection a node dials, or dials one a node's listener can accept); the
  target configuration, Linux 7.0 with its default sysctls and Go 1.27.3 (measured in
  `examples/net/semantics/`); valid addresses (D20, `addrOk`, which the proof checks by `decide`).
* **One host**: the address is a loopback address, which reaches only its own host. The model has no
  hosts (any machine may dial any valid address), so the theorem's machines are processes of one
  host, as `examples/net/shutdown/process_test.go` runs them.
* **Trusted**: the models of the `net` functions and types the program calls
  (`Net/TrustedCode/net.lean`, over `netExt`, with their struct-field facts `net.FieldAssumptions`),
  `Impl.lean`'s semantics, Perennial's Goose translation and Go semantics (`go.Semantics`; the
  commands' `Assumptions` are the generated unfoldings of the translated bodies), and `Robust`.
  Tracked by `etc/tcb-collections/net.txt`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

attribute [local instance] netExts netExtsSemantics

section adequacy

variable [GoGlobalContext]

/-- **`shutdown_crash_safety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the system's machines, each of which may crash at any step and
restart, each a fresh Go process (`Robust`'s premise): in every execution, of any length, no
thread of any machine is stuck and none has an unrecovered panic. -/
def shutdown_crash_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : cmd.node.Assumptions]
    [field_sem : net.FieldAssumptions] (σ0 : state) (g : GlobalState) (bound : Nat),
    Robustness.Robust (system σ0) [] g (threads := bound + 1) (bound := bound)

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

end
