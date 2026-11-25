/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Tag.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: `gryffproto.Tag.Compare` and `GreaterThan` (`tupaqproto.go`)
-/
module

public import Dsverify.Proof.gryff.X.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.replica2 (tagOf)

theorem cmp_char (a b : model.Tag) :
    a.cmp b = if sint.Z a.ts < sint.Z b.ts ∨ (a.ts = b.ts ∧ sint.Z a.cid < sint.Z b.cid) ∨
        (a.ts = b.ts ∧ a.cid = b.cid ∧ sint.Z a.rmwc < sint.Z b.rmwc) then -1
      else if a.ts = b.ts ∧ a.cid = b.cid ∧ a.rmwc = b.rmwc then 0 else 1 := by
  unfold model.Tag.cmp model.slt
  by_cases h1 : sint.Z a.ts < sint.Z b.ts <;> by_cases h2 : a.ts = b.ts <;>
    by_cases h3 : sint.Z a.cid < sint.Z b.cid <;> by_cases h4 : a.cid = b.cid <;>
    by_cases h5 : sint.Z a.rmwc < sint.Z b.rmwc <;> by_cases h6 : a.rmwc = b.rmwc <;>
    simp [h1, h2, h3, h4, h5, h6]

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gp_sem : src.gryffproto.Assumptions]

set_option goose.wp.extras true

theorem wp_Tag_Compare (a : Loc) (ta tb : src.gryffproto.Tag) :
    {{ (a ↦ ta : IProp GF) }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Compare")) (Val #tb))
    {{ (r : w64), RET #r; a ↦ ta ∗ ⌜sint.Z r = (tagOf ta).cmp (tagOf tb)⌝ }} := by
  wp_start as Ha
  wp_auto
  repeat' (first | wp_if_destruct | (wp_auto; done) | wp_auto)
  all_goals (iapply HΦ; iframe; ipureintro)
  all_goals (rw [cmp_char]; simp only [tagOf, ← BitVec.toInt_inj, sint.Z] at *)
  all_goals (split <;> (try split) <;>
    first | decide | (exfalso; omega))

theorem wp_Tag_GreaterThan (a : Loc) (ta tb : src.gryffproto.Tag) :
    {{ (a ↦ ta : IProp GF) }}
      (App (Val (a @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"GreaterThan"))
        (Val #tb))
    {{ RET #((tagOf ta).gt (tagOf tb)); a ↦ ta }} := by
  wp_start as Ha
  wp_auto
  wp_apply wp_Tag_Compare a ta tb $$ [$Ha] as %r ⟨Ha, %Hr⟩
  have : (tagOf ta).gt (tagOf tb) = decide (sint.Z (W64 0) < sint.Z r) := by
    unfold model.Tag.gt; rw [← Hr]; simp
  rw [← this]
  iapply HΦ; iframe

end

end Perennial.gryff.X
