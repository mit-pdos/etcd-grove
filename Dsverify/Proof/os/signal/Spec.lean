/-
(The lab's `Harness/Proof/os/signal.lean`, run `rabia-r1wake-1`.) `os/signal`'s specs Rabia's
code uses, as **hypotheses** (notes/dsv-rabia.md, "The hypotheses"): `os/signal` is translated
names only in the part (the lab proved these over its model, `harness/models/os/signal`, which
delivers no signal), so the specs are premises, carried by every theorem that calls them up to the
kit's closed statement. Two classes, kept apart on purpose:

* `Hyps` (**library specs**): `Notify.spec`, what `signal.Notify(c, sig...)` does in Go: it
  registers `c` with the runtime, which may from then on send any signal value on it (so every
  value the channel's protocol `P` allows: `□ ∀ s, P s`); `Stop.spec`: nothing.
* `NoSignals` (**an environment assumption, not a library spec**): nobody sends the kit's
  processes SIGINT or SIGTERM (the deployment's operator does not, and the network adversary of
  `Robust` cannot), so a registered channel never receives a signal: `NotifyQuiet.spec`, `Notify`
  with no requirement on the channel's protocol. It is what `internal/system.SigListen` uses: its
  signal channel's protocol is `False`, so its signal branch (which closes the server's `Done`) is
  unreachable. Without it (only `Hyps.Notify`), `SigListen` may close `Done`, and every routine
  that selects on `Done` (the tcp endpoints', the layers') would have to be proved for a closed
  `Done` (notes/dsv-rabia.md, "For the user").
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

/-- `Notify(c, sig...)` (the library's behavior): `c` is registered; the runtime may later send
any signal value on it, which `c`'s protocol must allow. -/
abbrev Notify.spec : Prop :=
  ∀ (c : GoChan) (γ : ChanNames) (P : os.Signal → IProp GF) (sig : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.os.signal ∗ isChanBag γ c P ∗ □ (∀ s, P s) }}
      (App (App (Val (@! os.signal.Notify)) (Val #c)) (Val #sig))
    {{ RET #(); True }}

/-- `Notify(c, sig...)` on a non-`nil` channel in a deployment where no signal is sent: nothing
(the environment assumption `NoSignals`, the header). -/
abbrev NotifyQuiet.spec : Prop :=
  ∀ (c : GoChan) (sig : GoSlice), c ≠ chan.nil →
    {{ isPkgInit (PROP := IProp GF) pkg_id.os.signal }}
      (App (App (Val (@! os.signal.Notify)) (Val #c)) (Val #sig))
    {{ RET #(); True }}

/-- `Stop(c)`: nothing. -/
abbrev Stop.spec : Prop :=
  ∀ (c : GoChan),
    {{ isPkgInit (PROP := IProp GF) pkg_id.os.signal }}
      (App (Val (@! os.signal.Stop)) (Val #c))
    {{ RET #(); True }}

end spec

/-- **The library hypotheses** (the header): `os/signal`'s specs. -/
class Hyps [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  Notify : Notify.spec (GF := GF)
  Stop : Stop.spec (GF := GF)

/-- **The environment assumption** (the header): no signal is sent to the deployment's
processes, so `Notify` registers a channel that never receives one. An assumption about how the
kit is run (nobody sends SIGINT/SIGTERM), not a property of `os/signal`'s code. -/
class NoSignals [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  notifyQuiet : NotifyQuiet.spec (GF := GF)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

theorem Notify.wp_proof [h : Hyps GF] : Notify.spec (GF := GF) := h.Notify
theorem NotifyQuiet.wp_proof [h : NoSignals GF] : NotifyQuiet.spec (GF := GF) := h.notifyQuiet
theorem Stop.wp_proof [h : Hyps GF] : Stop.spec (GF := GF) := h.Stop

end proof

end Perennial.os.signal
