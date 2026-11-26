/-
`csInvI`'s accessor with a value that follows the state (`csI_accA`): the caller's token at the
state `s` has the value `av s`, and closing at `s'` moves the value to `av s'`. For a step whose
abstract value changes with it (bbolt's commit ends at its second `fdatasync`: the value goes from
committing to idle as the sync lands). `csI_acc` (`CrashStIOps.lean`) is the case of a constant
`av`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.CrashStIL

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {A : Type} [Pos.Countable A]

/-- **`csInvI`'s accessor, the value following the state** (see the file header). -/
theorem csI_accA (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (av : CSt → A) :
    CsAcc (L := L) N (csInvI (L := L) N i γ γa γc Ok) (fun s => csTokI γ γa (av s) s)
      (fun s => Ok (av s) s) i := by
  unfold CsAcc
  intro E s hE
  unfold csTokI
  iintro #Hinv ⟨Hv, Ha⟩
  imod csInvI_open N i γ γa γc Ok s (av s) E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, %Hok, Hclose⟩
  imodintro
  iframe Hr
  isplitr
  · ipureintro; exact Hok
  iintro %s' %hs' Hr'
  imod ghostVar_update_halves s' γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod ghostVar_update_halves (av s') γa _ _ $$ Ha Ha' with ⟨Ha, Ha'⟩
  imod Hclose $$ [Hv' Ha' Hr'] with -
  · inext; unfold csInvIBody; ileft; iexists s', av s'; iframe; ipureintro; exact hs'
  imodintro
  dsimp only
  iframe

/-- The local caller's part over two tokens that agree at its state. -/
theorem csOwnL_tok (Tok Tok' : CSt → IProp GF) (i : Ino) (s : CSt) (h : Tok s = Tok' s) :
    csOwnL (L := L) Tok i s ⊢ csOwnL (L := L) Tok' i s := by
  unfold csOwnL; rw [h]

end acc

end Perennial
