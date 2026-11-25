/-
The proof of `badStringError` (`Net/Spec/net/http/badStringError.lean`): `fmt.Errorf` of two strings.
-/
module

public import Net.Spec.net.http.badStringError
public import Perennial.Spec.fmt.Errorf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem badStringError.wp_proof (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    badStringError.spec (GF := GF) (hG := hG) := by
  intro what val
  wp_start as #Hfmt
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_Errorf _ _ _ _ $$ [$Hsl] as %e ⟨-, %s, %Hout, Hee⟩
  · iapply fmt.argsOk_of_argsWf
    rw [show sint.nat (W64 (0 + 1)) = 1 from rfl]
    exact fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)
  iunfold fmt.errorfErr at Hee
  icases Hee with ⟨⟨%Hptr, -⟩, -, Hm⟩
  obtain ⟨ds, hds, hw⟩ : ∃ ds, fmt.fmtDirectives go!"%s %q" = some ds ∧ fmt.wrapArgs ds 2 = [] :=
    ⟨_, rfl, rfl⟩
  simp only [hds, List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, hw]
  icases Hm with ⟨%l, %hl, #Hl⟩
  iapply HΦ
  isplitr
  · ipureintro
    obtain ⟨T, l, hT, hl⟩ := Hptr
    intro ii T' h hty
    cases h
    exact ⟨l, hl⟩
  iexists l, s
  iframe Hl
  ipureintro
  exact ⟨hl, fmt.SprintfOut.str_prefix what go!" %q" _ s Hout⟩

end proof

end net.http
end Perennial
