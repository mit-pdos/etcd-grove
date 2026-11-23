/-
(The lab's `Harness/Proof/os/signal.lean`, run `rabia-r1wake-1`.) The `os/signal` spec Rabia's
code uses, as a **hypothesis** (notes/dsv-rabia.md, "The hypotheses"): `os/signal` is translated
names only in the part (the lab proved its specs over its model, `harness/models/os/signal`, which
delivers no signal), so the spec is a premise, carried by every theorem that calls it up to the
kit's closed statement.

`NoSignals` (**an environment assumption, not a library spec**): nobody sends the kit's processes
SIGINT or SIGTERM (the deployment's operator does not, and the network adversary of `Robust`
cannot). So a channel registered for exactly those two signals never receives one:
`NotifyQuiet.spec`, `Notify(c, SIGINT, SIGTERM)` with no requirement on the channel's protocol.
The signal list is part of the precondition (#24): Go's `Notify(c)` with no signals relays every
signal, the runtime's own included (`SIGURG` for preemption, golang/go#37942; `SIGCHLD`,
`SIGPIPE`), whatever the operator does, and other signals than these two are not covered by the
assumption. It is what `internal/system.SigListen` uses (`signal.Notify(sigIn, syscall.SIGINT,
syscall.SIGTERM)`): its signal channel's protocol is `False`, so its signal branch (which closes
the server's `Done`) is unreachable. Without it, `SigListen` may close `Done`, and every routine
that selects on `Done` (the tcp endpoints', the layers') would have to be proved for a closed
`Done` (notes/dsv-rabia.md, "For the user"). `signal.Stop` needs no spec: `SigListen` reaches it
only after a receive from one of the two channels, neither of which ever sends.
-/
module

public import Dsverify.Proof.os.signal.Base
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

noncomputable section

namespace Perennial.os.signal

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The signals `internal/system.SigListen` registers, as the `os.Signal` values of its slice
literal: `syscall.SIGINT` (2) and `syscall.SIGTERM` (15). -/
def quietSigs : List os.Signal :=
  [interface.mkOk syscall.Signal.ty #(W64 2), interface.mkOk syscall.Signal.ty #(W64 15)]

/-- `Notify(c, SIGINT, SIGTERM)` on a non-`nil` channel in a deployment where neither signal is
sent: nothing (the environment assumption `NoSignals`, the header). -/
abbrev NotifyQuiet.spec : Prop :=
  ∀ (c : GoChan) (sig : GoSlice) (dq : DFrac), c ≠ chan.nil →
    {{ isPkgInit (PROP := IProp GF) pkg_id.os.signal ∗ sig ↦*{dq} quietSigs }}
      (App (App (Val (@! os.signal.Notify)) (Val #c)) (Val #sig))
    {{ RET #(); sig ↦*{dq} quietSigs }}

end spec

/-- **The environment assumption** (the header): SIGINT and SIGTERM are not sent to the
deployment's processes, so `Notify` registers a channel for exactly those two that never receives
one. An assumption about how the kit is run, not a property of `os/signal`'s code. -/
class NoSignals [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  notifyQuiet : NotifyQuiet.spec (GF := GF)

end Perennial.os.signal
