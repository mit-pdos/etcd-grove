/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/system/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/internal/system`'s spec (interface, stage 1a): `SigListen(done)` returns only if `done` is
closed or a signal arrives; with the `os/signal` model (no signal is ever delivered) and a `done`
channel nobody sends on or closes (a bag channel whose values are `False`), it never returns.
-/
module

public import Dsverify.GeneratedProof.rabia.internal.system
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Dsverify.Proof.rabia.internal.system.Base



@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.system

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.system.Assumptions]

/-- `SigListen(done)`, `done` never sent on nor closed: it does not return. -/
abbrev SigListen.spec : Prop :=
  ∀ (done : GoChan) (γ : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.system ∗
      isChanBag (V := Unit) γ done (fun _ => iprop(False)) }}
    (App (Val (@! SigListen)) (Val #done))
  {{ RET #(); False }}

end spec

end Perennial.rabia.internal.system
