/-
**Trust-boundary axioms** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `signal.Notify(c, sigs...)` on
a non-`nil` channel, for the two signal lists the kits pass, registers a channel that **never
receives** (`os.signal.NotifyQuiet.spec`, `Spec.lean`), under an **environment claim**: nobody sends
the deployment's processes any of those signals (the operator does not, and the network adversary
of `Robust` cannot send signals). `os/signal` is translated names only in the part. What Go's
`Notify` itself does (`signal.go`): it panics only on a `nil` channel (excluded: `c ≠ chan.nil`),
records `c` in the handler table under the package's lock, and enables the signals in the runtime;
a signal is then delivered to `c` only when the process receives it. So with none of `sigs` sent,
`c` never receives one. `sigs` must not be empty: `Notify(c)` with no signals relays every signal,
the runtime's own included (`SIGURG` for preemption), whatever the operator does (`NotifyQuiet.spec`
asks `sigs ≠ []`).
* `wp_proofQuietSigs`: rabia's `internal/system.SigListen`, `signal.Notify(sigIn, syscall.SIGINT,
  syscall.SIGTERM)`: nobody sends SIGINT or SIGTERM (the statement premise `os.signal.NoSignals
  os.signal.quietSigs` of rabia until dsv-fix4).
* `wp_proofUsr1Sigs`: SwiftPaxos's `hook.HookUser1`, `signal.Notify(c, syscall.Signal(0xa))`: nobody sends
  SIGUSR1 (the premise `os.signal.NoSignals usr1Sigs` of swiftpaxos until dsv-fix4).
Each states exactly its class's field, for its list only. Review:
`notes/axiom-review/dsv-fix4/os-signal-notify.md`.
-/
module

public import Dsverify.Proof.os.signal.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom, environment claim** (the file header): nobody sends SIGINT or SIGTERM. -/
axiom os.signal.Notify.wp_proofQuietSigs : os.signal.NotifyQuiet.spec (GF := GF) os.signal.quietSigs

/-- **Trust-boundary axiom, environment claim** (the file header): nobody sends SIGUSR1. -/
axiom os.signal.Notify.wp_proofUsr1Sigs : os.signal.NotifyQuiet.spec (GF := GF) os.signal.usr1Sigs

end ax

end Perennial
