/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/PkgState.lean`, run `rabia-r1wake-1`,
redesigned for remote's machines and generated initializers; notes/dsv-rabia.md.)

The lab chose one record of package states for all its nodes (`RabiaNetPkgState`) and proved each
package's initialization against it; here each package's fact is its `Base.lean`'s and its
initialization is generated (`etc/gen-init.py`). What is left of the lab's file is the claim of
`config.Conf`: the package fact keeps `Conf`'s points-to in an invariant (`config.confInv`,
`internal/config/Base.lean`), and the machine's one `configure` (a client machine's `newClient`, a
server machine's `serveAt`) claims it with its package state (`ownGoState`, exclusive on the
machine; the boot hands it to `main` after the initialization). The lab's invariant had three
states and told the claimers apart by their node's IP (its client nodes claimed with their
address's unset protocol, its servers with their package state); on remote's machines, all on one
host, every claimer uses its package state, so two states suffice.

The lab's `message` package state (`msgState`: its errors, the `MsgType` maps, the file
descriptor) is not `message`'s fact yet (its fact is `True`): added with the proof that needs it.
-/
module

public import Dsverify.Proof.rabia.internal.config.Base

@[expose] public section

noncomputable section

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode rabia.internal.config

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]

/-- Two `ownGoState`s contradict: each holds the full authority of the initialized-packages map. -/
theorem ownGoState_excl {GF' : BundledGFunctors} [hS : GoStateGS GF'] (σ1 σ2 : GMap GoString Bool) :
    ownGoState (GF := GF') σ1 ∗ ownGoState σ2 ⊢ (False : IProp GF') := by
  letI := hS.package_mono_allG
  unfold ownGoState
  iintro ⟨⟨-, H1, -⟩, ⟨-, H2, -⟩⟩
  ihave %h := ghostMapAuth_valid_2 _ _ _ _ _ $$ H1 H2
  exfalso
  have h1 := h.1
  first
    | (revert h1; grind)
    | (have h2 : ((1 : Qp) + 1).val ≤ (1 : Qp).val := h1; revert h2; simp; grind)

/-- A machine's `configure` claims `Conf`'s points-to with its package state (the lab's
`confClaimServer`): the invariant is then in the claimer's state for good. -/
theorem confClaim (E : CoPset) (hE : ↑confN ⊆ E) (σ : GMap GoString Bool) :
    inv confN (confInv (GF := GF) (hG := hG)) ∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ ⊢
      |={E}=> (globalAddr Conf ↦ (zeroValDef : Config)) := by
  iintro ⟨#Hinv, Hσ⟩
  iinv Hinv with Hi Hclose
  unfold confInv
  icases Hi with (>HC | ⟨%σ', >Hσ'⟩)
  · imod Hclose $$ [Hσ] with -
    · inext
      iright
      iexists σ
      iexact Hσ
    imodintro
    iexact HC
  · iexfalso
    iapply ownGoState_excl $$ [Hσ Hσ']
    iframe

end spec

end Perennial.rabia
