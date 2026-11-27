/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the top-level robustness result, stated

**net/http's driver, closed** (`examples/net/httpdriver`, notes/library-drivers.md): two machines,
neither of which crashes -- the server (`cmd/server`: a `ServeMux` with the handlers `/echo` and
`/status`, served with `http.Serve` at `Addr`) and the client (`cmd/client`: opens random
connections from concurrent goroutines, writes random HTTP/1.1 requests on each, reads each response
with `http.ReadResponse` and its body to the end, and panics if a response contradicts what net/http's
server guarantees: the driver's sections echo, status, mux, bad-request, keep-alive,
concurrent-connections) -- deployed at `httpAddrs` (`DistDeploy`: the address valid, no connection,
no listener). In every execution of fewer than `httpSteps` steps along which every machine keeps fewer
than `httpThreads` live threads (the two bounds, with why, in `TopLevelDefs.lean`), no thread of
either machine is stuck and none has a top-level panic (`Robust`, `Robustness/Statement.lean`), each
machine a fresh Go process (`Robust`'s premise). Since the client panics when a property of net/http
fails, this says each holds, under every fault the net extension allows (cut, reset or delayed
connections, refused dials).

**Premises**: the deployment's start (`DistDeploy`), the environment premise
`GodebugHttpmuxgo121Not1` (on every machine of the deployment, `GODEBUG` does not set `httpmuxgo121=1`:
the setting is one constant for all machines, `Net/TrustedCode/net/http.lean`; the server's `ServeMux`
runs Go 1.22's matcher, the one proved; #18's option (a)), and the program's
typing facts (the commands' `Assumptions`, `go.BasicIntoValInj`; `net.FieldAssumptions` went with the Go-model net). What it rests
on beyond the proofs, besides the net extension's semantics and the net/http model's trusted claim:
the trust-base collection `etc/tcb-collections/httpdriver.txt`.
Proved in `Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/httpdriver/TopLevelRobustness.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- See the file header. -/
def httpdriver_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [srv_sem : cmd.server.Assumptions] [cli_sem : cmd.client.Assumptions]
    [go.BasicIntoValInj]
    (σs σc : state) (g : GlobalState) (HEnv : net.http.GodebugHttpmuxgo121Not1),
    DistDeploy httpAddrs (system σs σc) g →
    Robustness.Robust [] (system σs σc) g httpThreads httpSteps

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
