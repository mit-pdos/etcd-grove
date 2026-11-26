/- Lean-first (no Rocq counterpart).

# `net/acceptloop`: the top-level robustness result, stated

`acceptloop_crash_robust`: the two nodes, `cmd/server` and `cmd/client`, at `127.0.0.1:7103`
(`examples/net/acceptloop/`), each a machine that may crash and restart, satisfy the generic
robustness statement (`Robustness/Statement.lean`, `Robust`): in every execution of fewer than
`bound` steps, no thread of any machine is stuck and none has an unrecovered panic, so each of the
client's calls' check (`acceptloop.CallOne`: the reply is its own id) never fails. The number of
calls is drawn at random (`wire.RandomInt`); `examples/net/acceptloop/control_test.go` shows the
check fires against a server that replies with another id. This file only states it (to audit); the
proof is in
`Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/acceptloop/TopLevelRobustness.lean`.

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
  host, as `examples/net/acceptloop/process_test.go` runs them.
* **Trusted**: the models of the `net` functions and types the program calls
  (Go's `net` over its Go model `models/net`, whose primitive stubs `Net/TrustedCode/net.lean` models over `netExt`),
  `Impl.lean`'s semantics, Perennial's Goose translation and Go semantics (`go.Semantics`; Goose's
  model of `primitive.RandomUint64`, any `uint64`; the commands' `Assumptions` are the generated
  unfoldings of the translated bodies), and `Robust`. Tracked by `etc/tcb-collections/net.txt`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

attribute [local instance] netExts netExtsSemantics

section adequacy

variable [GoGlobalContext]

/-- **`acceptloop_crash_safety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the system's machines, each of which may crash at any step and
restart, each a fresh Go process (`Robust`'s premise): in every execution, of any length, no
thread of any machine is stuck and none has an unrecovered panic. -/
def acceptloop_crash_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [server_sem : cmd.server.Assumptions]
    [client_sem : cmd.client.Assumptions]
    (σs σc : state) (g : GlobalState) (bound : Nat),
    Robustness.Robust (system σs σc) [] g (threads := bound + 1) (bound := bound)

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial

end
