/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/LockBoot.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B: the run loop's first `Lock` (`lock_boot`'s proof, with the replica's prophecy cell:
hub request B-R5) and `loopTok`'s laws.
-/
module

public import Dsverify.Proof.gryff.Replica2.State

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model kahn pure replica2
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The empty trace's state. -/
theorem stOf_nil (k : Fin 3) : pure.stOf k [] = model.RState.init k.val := rfl

/-- The initial state's id. -/
theorem init_id (k : Fin 3) : (model.RState.init k.val).id = replica2.rid32 k := rfl

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics] [fa : src.fastrpc.Assumptions]

/-- `lock_boot` with the replica's prophecy cell (B-R5: the lock's prophecy `p` is the one
`loopTok` holds the boot resources of). -/
theorem lock_boot_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (p : ProphId) :
    r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaLockInv γ ρ k r p ∗ loopTok γ ρ k r ⊢
      |==> ((∃ (t : List Ev) (xs : replica.XS), lockedAt γ ρ k r p t xs) ∗ loopTok γ ρ k r) := by
  iintro ⟨#Hp, Hli, Htok⟩
  unfold loopTok
  icases Htok with (Hb | ⟨Hb, Hrest, Hpo⟩)
  · unfold replicaLockInv
    icases Hli with (Hlk | Hlb)
    · imodintro
      iframe
    · unfold lockBoot
      icases Hlb with ⟨%h, %xs, -, -, -, Hb'⟩
      ihave %e := ghostVar_agree ρ.boot _ _ _ _ $$ Hb Hb'
      cases e
  · unfold replicaLockInv
    icases Hli with (⟨%t, %xs, Hlk⟩ | Hlb)
    · unfold lockedAt
      icases Hlk with ⟨-, -, -, -, Hb'⟩
      ihave %e := ghostVar_agree ρ.boot _ _ _ _ $$ Hb Hb'
      cases e
    · unfold lockBoot bootRest
      icases Hlb with ⟨%h, %xs, #Hh, Hep, Hxs, Hb'⟩
      icases Hrest with ⟨%p', %gR, %pa, %co, %h', #Hp', Ht, Hpr, #HgR, #Hpa, #Hco, #Hh',
        Hparti, Hval, Hcoord, Hprop, Hscr, %Hid⟩
      icombine Hp Hp' gives %Hpp
      subst Hpp
      imod ghostVar_update_halves false ρ.boot _ _ $$ Hb Hb' with ⟨Hb, Hb'⟩
      imodintro
      isplitr [Hb']
      · iexists [], xs
        unfold lockedAt
        iframe Ht Hpr Hpo Hb
        iapply (replicaOwnX_split ρ k r xs (pure.stOf k [])).2
        iexists gR, pa, co, h
        iframe
        iframe #
        ipureintro
        exact Hid
      · ileft
        iexact Hb'

end

end Perennial.gryff.unitB
