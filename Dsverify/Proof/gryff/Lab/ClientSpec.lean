/-
Ported from dsverify-lab examples/gryff/proof/Harness/ClientSpec.lean (run gryff-bump-1, lab master 915f964;
notes/dsv-gryff.md): the client namespace and the logically atomic client operation's
shapes (`opAwp`, `opAwpMaybe`) only, not `KitCode`/`ClientSpec` (the client is remote's here).

-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Net.Proto
public import Perennial.Golang.Theory
public import Iris.ProgramLogic.Atomic

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace dsverify_lab.harness

set_option linter.unusedSectionVars false

/-- The namespace reserved for clients: the outer mask of every client operation's atomic update.
A client allocates the invariants it opens to give the update under `clientN`; the
implementation allocates none there. -/
def clientN : Namespace := ndot nroot "dsv_client"

section aupd
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {TA TB : Tele}

/-- Weakening an atomic update's commit postcondition with a wand. The wand is available at both
the abort and the commit of each step (an `∧`), and used only at the commit. Not in iris-lean at
the pin (Rocq Iris has `atomic_update_wand`). -/
theorem aupd_wand {Eo Ei : CoPset} {α : TA.Arg → PROP} {β Φ1 Φ2 : TA.Arg → TB.Arg → PROP} :
    atomic_update Eo Ei α β Φ1 ∗ (∀.. x, ∀.. y, Φ1 x y -∗ Φ2 x y) ⊢
      atomic_update Eo Ei α β Φ2 := by
  change _ ⊢ bi_greatest_fixpoint (atomic_update_pre Eo Ei α β Φ2) ()
  iintro ⟨HAU, HW⟩
  iapply greatest_fixpoint_coiter (atomic_update_pre Eo Ei α β Φ2)
    (fun _ => iprop(atomic_update Eo Ei α β Φ1 ∗ (∀.. x, ∀.. y, Φ1 x y -∗ Φ2 x y))) $$ [] [HAU HW]
  · iintro !> %_ ⟨H, HW⟩
    unfold atomic_update_pre
    ihave H := aupd_aacc $$ H
    iapply atomic_acc_wand $$ [HW] H
    isplit
    · iintro H
      dsimp only
      iframe H HW
    · iintro %x %y H1
      iapply HW $$ H1
  · iframe HAU HW

end aupd

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Unknown outcome A: `e` is logically atomic, with its update at outer mask `Eo`, from
`α σ` to `β σ σ' o`; it returns `ret o` and hands back `POST`. -/
def opAwp {S O : Type} (e : Expr) (Eo : CoPset) (α : S → IProp GF) (β : S → S → O → IProp GF)
    (ret : O → val) (POST : IProp GF) : IProp GF :=
  iprop(∀ Φ, AU <{ ∃∃ σ, α σ }> @ Eo, ∅ <{ ∀∀ σ' o, β σ σ' o, COMM (POST -∗ Φ (ret o)) }> -∗
    WP e {{ Φ }})

/-- Unknown outcome B: `e` is logically atomic as in `opAwp`, or it returns an error value `v`
(`isErr v`), after which the update may or may not have been committed, or may be committed later.
The client picks the commit's postcondition `Q` (a receipt, or resources taken from its invariant
at the commit); `e`'s own postcondition is fixed, so a caller keeps its local resources by the
frame rule. On a normal return `v = ret o` the client gets `Q σ σ' o` of the commit. -/
def opAwpMaybe {S O : Type} (e : Expr) (Eo : CoPset) (α : S → IProp GF)
    (β : S → S → O → IProp GF) (ret : O → val) (isErr : val → Prop) (POST : IProp GF) :
    IProp GF :=
  iprop(∀ (Q : S → S → O → IProp GF),
    AU <{ ∃∃ σ, α σ }> @ Eo, ∅ <{ ∀∀ σ' o, β σ σ' o, COMM Q σ σ' o }> -∗
    WP e {{ v, POST ∗ ((∃ σ σ' o, ⌜v = ret o⌝ ∗ Q σ σ' o) ∨ ⌜isErr v⌝) }})

theorem opAwpMaybe_of_opAwp {S O : Type} {e : Expr} {Eo : CoPset} {α : S → IProp GF}
    {β : S → S → O → IProp GF} {ret : O → val} {POST : IProp GF} (isErr : val → Prop) :
    opAwp e Eo α β ret POST ⊢ opAwpMaybe e Eo α β ret isErr POST := by
  unfold opAwp opAwpMaybe
  iintro H %Q AU
  iapply H
  iapply aupd_wand
  isplitl [AU]
  · iexact AU
  iintro %x %y
  rcases x with ⟨σ, ⟨⟩⟩
  rcases y with ⟨σ', o, ⟨⟩⟩
  dsimp only [Tele.app]
  iintro HQ HPOST
  iframe HPOST
  ileft
  iexists σ, σ', o
  iframe HQ
  ipureintro; rfl

theorem opAwp_of_opAwpMaybe {S O : Type} {e : Expr} {Eo : CoPset} {α : S → IProp GF}
    {β : S → S → O → IProp GF} {ret : O → val} {POST : IProp GF} :
    opAwpMaybe e Eo α β ret (fun _ => False) POST ⊢ opAwp e Eo α β ret POST := by
  unfold opAwp opAwpMaybe
  iintro H %Φ AU
  ihave Hwp := H $$ %(fun _ _ o => iprop(POST -∗ Φ (ret o))) AU
  iapply wp_wand $$ Hwp
  iintro %v ⟨HPOST, H⟩
  icases H with (⟨%σ, %σ', %o, %Hv, HQ⟩ | %Hf)
  · subst Hv
    iapply HQ $$ HPOST
  · exact Hf.elim

end defs

end dsverify_lab.harness

end Perennial
