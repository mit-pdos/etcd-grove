/-
The proof of `ParseHTTPVersion` (`Net/Spec/net/http/ParseHTTPVersion.lean`): the switch's two cases.
-/
module

public import Net.Spec.net.http.ParseHTTPVersion
public import Perennial.Spec.strings.HasPrefix
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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

/-- A strict prefix of either version is shorter than `"HTTP/X.Y"`. -/
theorem vers_short {vers : GoString} (h : vers <+: go!"HTTP/1.0" ∨ vers <+: go!"HTTP/1.1")
    (h0 : vers ≠ go!"HTTP/1.0") (h1 : vers ≠ go!"HTTP/1.1") : vers.length < 8 := by
  rcases h with h | h
  · have := h.length_le
    rcases Nat.lt_or_eq_of_le this with h' | h'
    · simpa using h'
    · exact absurd (h.eq_of_length h') h0
  · have := h.length_le
    rcases Nat.lt_or_eq_of_le this with h' | h'
    · simpa using h'
    · exact absurd (h.eq_of_length h') h1

theorem ParseHTTPVersion.wp_proof (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    ParseHTTPVersion.spec (GF := GF) (hG := hG) := by
  intro vers
  wp_start as ⟨#Henv, %Hv⟩
  ihave #Hstr := httpEnv_strings $$ Henv
  wp_auto
  by_cases h1 : vers = go!"HTTP/1.1"
  · subst h1
    simp (config := { decide := true }) only [↓reduceIte]
    wp_auto
    iapply HΦ; ipureintro; decide
  by_cases h0 : vers = go!"HTTP/1.0"
  · subst h0
    simp (config := { decide := true }) only [↓reduceIte]
    wp_auto
    try simp (config := { decide := true }) only [↓reduceIte]
    try wp_auto
    iapply HΦ; ipureintro; decide
  simp only [decide_eq_false h1]
  wp_auto
  simp only [decide_eq_false h0]
  wp_auto
  wp_apply wp_HasPrefix $$ Hstr
  have hs := vers_short Hv h0 h1
  try wp_auto
  wp_if_destruct
  all_goals try ((try wp_auto); iapply HΦ; ipureintro; simp [h0, h1]; done)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len vers with %Hl
  try wp_auto
  wp_if_destruct
  all_goals try ((try wp_auto); iapply HΦ; ipureintro; simp [h0, h1]; done)
  exfalso
  rename_i Hif
  revert Hif; word

end proof

end net.http
end Perennial
