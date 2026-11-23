/-
(The lab's `Harness/Proof/os/signal.lean`, run `rabia-r1wake-1`.) `os/signal`'s specs Rabia's
code uses, as **hypotheses** (notes/dsv-rabia.md, "The hypotheses"): `os/signal` is translated
names only in the part (the lab proved these over its model, `harness/models/os/signal`, which
delivers no signal), so the specs are the fields of the class `Hyps` (a `Prop`), which every theorem
that calls them takes as an instance argument, up to the kit's closed statement.

`Notify.spec` says that no signal is delivered to the channel: an **assumption on the
environment** (nobody sends the kit's processes SIGINT or SIGTERM; the network adversary of
`Robust` cannot send signals), not a property of `os/signal`'s code. `Stop` does nothing.
-/
module

public import Dsverify.Proof.os.signal.Base

@[expose] public section

noncomputable section

namespace Perennial.os.signal

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `Notify(c, sig...)` on a non-`nil` channel: nothing (no signal is delivered: the header). -/
abbrev Notify.spec : Prop :=
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

/-- **The hypotheses** (the header). -/
class Hyps [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  Notify : Notify.spec (GF := GF)
  Stop : Stop.spec (GF := GF)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

theorem Notify.wp_proof [h : Hyps GF] : Notify.spec (GF := GF) := h.Notify
theorem Stop.wp_proof [h : Hyps GF] : Stop.spec (GF := GF) := h.Stop

end proof

end Perennial.os.signal
