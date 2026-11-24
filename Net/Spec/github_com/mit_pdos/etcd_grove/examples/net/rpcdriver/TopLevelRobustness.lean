/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the top-level robustness result, stated

**net/rpc's driver, closed** (`examples/net/rpcdriver`, notes/library-drivers.md): two machines,
neither of which crashes -- the server (`cmd/server`: registers the driver's service, then serves
it with net/rpc over raw TCP, `rpc.Accept` at `TCPAddr`, and over HTTP, `rpc.HandleHTTP` and
`http.Serve` at `HTTPAddr`) and the client (`cmd/client`: dials either way at random, makes random
`Call`/`Go` calls from concurrent workers, closes, and panics if an outcome contradicts what
net/rpc guarantees: the driver's sections register, dial, call-success, server-error,
other-errors, concurrent-calls, close) -- deployed at `rpcAddrs` (`DistDeploy`: the addresses
distinct and valid, no connection, no listener). In every execution of fewer than `rpcStepBound`
steps (`2 ^ 31 - 1`: net/rpc's server's thread bound, `TopLevelDefs.lean`), with any number of
threads, no thread of either machine is stuck and none has a top-level panic (`Robust`,
`Robustness/Statement.lean`), each machine a fresh Go process (`Robust`'s premise). Since the
client panics when a property of net/rpc fails, this says each holds, under every fault the net
extension allows (cut, reset or delayed connections, refused dials).

**Premises**: only the deployment's start (`DistDeploy`) and the program's typing facts (the
commands' `Assumptions`, `net.FieldAssumptions`, `go.BasicIntoValInj`), as echo's and the kits'
statements. What it rests on beyond the proofs, besides the net extension's semantics and the
net/rpc and net/http models' trusted claims: the trust-base collection
`etc/tcb-collections/rpcdriver.txt` (the interim axioms of net/rpc's and net/http's initializers,
`Net/Proof/net/{rpc,http}/Init.lean`).
Proved in `Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/TopLevelRobustness.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- See the file header. -/
def rpcdriver_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [srv_sem : cmd.server.Assumptions] [cli_sem : cmd.client.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σs σc : state) (g : GlobalState) (threads : Nat),
    DistDeploy rpcAddrs (system σs σc) g →
    Robustness.Robust [] (system σs σc) g threads rpcStepBound

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
