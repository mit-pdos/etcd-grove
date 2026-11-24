/-
The proof of `modelParseRequestURI` (`Net/Spec/net/http/modelParseRequestURI.lean`): on a `reqPath`
the first branch is taken (`modelPathBytes` is true), and the URL literal allocated.
-/
module

public import Net.Spec.net.http.modelParseRequestURI
public import Net.Spec.net.http.modelPathBytes
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelParseRequestURI.wp_proof (Hbytes : modelPathBytes.spec (GF := GF) (hG := hG)) :
    modelParseRequestURI.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as %Hs
  obtain ⟨Hhd, Hall⟩ := Hs
  obtain ⟨c, s', rfl⟩ : ∃ c s', s = c :: s' := by
    cases s with
    | nil => simp at Hhd
    | cons c s' => exact ⟨c, s', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at Hhd
  subst Hhd
  wp_auto
  wp_apply wp_string_len as %Hl
  have hpos : sint.Z (W64 0) < sint.Z (W64 ((W8 47 :: s').length : Int)) := by
    simp only [List.length_cons] at Hl ⊢; word
  simp only [hpos, _root_.decide_true]
  wp_auto
  wp_apply Hbytes
  rw [show (W8 47 :: s').all pathByte = true from List.all_eq_true.mpr Hall]
  wp_auto
  iapply HΦ; iexact «$r0»

end proof

end net.http
end Perennial
