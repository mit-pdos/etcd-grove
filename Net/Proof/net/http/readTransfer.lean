/-
The proof of `readTransfer` (`Net/Spec/net/http/readTransfer.lean`), on a header map without
`Transfer-Encoding`, `Content-Length` or `Trailer`. A `*Response` to a request other than `HEAD`:
`shouldClose` (the header possibly without `Connection` after it, which keeps the other keys absent),
no transfer encoding, no `Content-Length`, no trailer; the body is `NoBody` (`fixLength`'s `0`) or a
`body` reading `r` to the connection's end (`-1`, which closes). A `*Request`: `fixLength`'s `0`, so
`NoBody` (`reqNoBody`). `bodyAllowedForStatus` is proved here (`wp_bodyAllowedForStatus`),
`noResponseBodyExpected` again (as in `fixLength.lean`: a proof file imports no proof).
-/
module

public import Net.Spec.net.http.readTransfer
public import Net.Spec.net.http.shouldClose
public import Net.Spec.net.http.transferReader__parseTransferEncoding
public import Net.Spec.net.http.fixLength
public import Net.Spec.net.http.fixTrailer

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

theorem wp_noResponseBodyExpected' (m : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! net.http.noResponseBodyExpected)) (Val #m))
    {{ RET #(decide (m = go!"HEAD")); True }} := by
  wp_start
  wp_auto
  iapply HΦ; itrivial

theorem decide_true_eq_decide (P : Prop) [Decidable P] : decide (true = decide P) = decide P := by
  by_cases h : P <;> simp [h]

theorem wp_bodyAllowedForStatus (st : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! net.http.bodyAllowedForStatus)) (Val #st))
    {{ (b : Bool), RET #b; True }} := by
  wp_start
  wp_auto
  all_goals
    repeat (first | wp_if_destruct | wp_auto)
  all_goals (try rw [decide_true_eq_decide (st = W64 204)])
  all_goals
    repeat (first | wp_if_destruct | wp_auto)
  all_goals (try rw [decide_true_eq_decide (st = W64 304)])
  all_goals
    repeat (first | wp_if_destruct | wp_auto)
  all_goals (iapply HΦ; itrivial)

set_option maxHeartbeats 1600000 in
theorem readTransfer.wp_proof
    (wp_shouldClose : shouldClose.spec (GF := GF) (hG := hG))
    (wp_pte : transferReader.parseTransferEncoding.spec (GF := GF) (hG := hG))
    (wp_fixLength : fixLength.spec (GF := GF) (hG := hG))
    (wp_fixTrailer : fixTrailer.spec (GF := GF) (hG := hG)) :
    readTransfer.spec (GF := GF) (hG := hG) := by
  constructor
  · intro resp rv ms r req rq dq maxT
    wp_start as ⟨#Henv, Hresp, Hh, Hcv, %Hks, %Hreq, Hrq, %Hm⟩
    ihave #Henv' := Henv
    iunfold httpEnv at Henv'
    icases Henv' with ⟨-, -, -, -, -, %nb, #Hnb⟩
    have hrv : rv = { rv with Request' := req } := by cases rv; cases Hreq; rfl
    rw [hrv]
    wp_auto
    simp only
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hrq
    wp_apply wp_shouldClose $$ [Hh Hcv] as %cl ⟨%ms', Hh, Hcv, %Hms'⟩
    · iframe
    have Hks' : ms' !! go!"Transfer-Encoding" = none ∧ ms' !! go!"Content-Length" = none ∧
        ms' !! go!"Trailer" = none := by
      rcases Hms' with rfl | ⟨-, rfl⟩
      · exact Hks
      · refine ⟨?_, ?_, ?_⟩ <;>
          (rw [GMap.lookup_delete_ne _ (by decide)]) <;> simp [Hks]
    have Hms'' : ms' = ms ∨ ms' = GMap.delete go!"Connection" ms := by
      rcases Hms' with h | ⟨-, h⟩ <;> simp [h]
    clear Hms'
    obtain ⟨Hte, Hcl, Htr⟩ := Hks'
    cases cl
    all_goals repeat (first | wp_if_destruct | wp_auto)
    all_goals try (exfalso; exact Hnn rfl)
    all_goals try simp only
    all_goals try (
      icases typedPointsto_split _ _ _ $$ Hrq with Hrq
      simp only [TypedPointsto.typedPointstoDef]
      icases Hrq with ⟨HMeth, Hrq⟩
      wp_auto
      ihave Hrq := typedPointsto_combine req rq dq Hnn $$ [HMeth Hrq]
      · simp only [TypedPointsto.typedPointstoDef]; iframe)
    all_goals repeat (first | wp_if_destruct | wp_auto | wp_load)
    all_goals try simp only
    all_goals
      wp_apply wp_pte _ _ ms' $$ [«$r0» Hh] as ⟨Htr, Hh⟩
      · iframe; ipureintro; exact Hte
    all_goals repeat (first | wp_if_destruct | wp_auto | wp_load)
    all_goals try simp only
    all_goals
      wp_apply wp_fixLength true _ _ _ ms' $$ [Hh] as %n ⟨%Hn, Hh⟩
      · iframe; ipureintro; exact ⟨fun _ => Hm, Hcl⟩
    all_goals rcases Hn with rfl | ⟨-, rfl⟩
    all_goals repeat (first | wp_if_destruct | wp_auto | wp_load)
    all_goals try (exfalso; exact Hm ‹rq.Method' = _›)
    all_goals try simp only
    all_goals
      wp_apply wp_fixTrailer _ ms' $$ [Hh] as Hh
      · iframe; ipureintro; exact Htr
    all_goals repeat (first | iintro - | wp_if_destruct | wp_auto | wp_load |
      wp_apply wp_bodyAllowedForStatus as %ba | wp_apply wp_noResponseBodyExpected' |
      wp_apply (IntoValTyped.wp_alloc (V := net.http.body) (t := net.http.body.ty)) as %lb Hlb)
    all_goals try simp only
    all_goals try wp_apply (IntoValTyped.wp_alloc (V := net.http.body) (t := net.http.body.ty)) as %lb Hlb
    all_goals repeat (first | iintro - | wp_if_destruct | wp_auto | wp_load)
    all_goals try simp only
    all_goals (iapply HΦ; iexists _, ms'; iframe; ipureintro; exact ⟨rfl, Hms''⟩)
  · intro req rqv ms r maxT
    wp_start as ⟨#Henv, Hreq, Hh, %Hks⟩
    obtain ⟨Hte, Hcl, Htr⟩ := Hks
    ihave #Henv' := Henv
    iunfold httpEnv at Henv'
    icases Henv' with ⟨-, -, -, -, -, %nb, #Hnb⟩
    wp_auto
    all_goals repeat (first | wp_if_destruct | wp_auto | wp_load)
    all_goals try simp only
    all_goals
      wp_apply wp_pte _ _ ms $$ [«$r0» Hh] as ⟨Htr', Hh⟩
      · iframe; ipureintro; exact Hte
    all_goals repeat (first | wp_if_destruct | wp_auto | wp_load)
    all_goals try simp only
    all_goals
      wp_apply wp_fixLength false _ _ _ ms $$ [Hh] as %n ⟨%Hn, Hh⟩
      · iframe; ipureintro; exact ⟨fun h => absurd h (by decide), Hcl⟩
    all_goals rcases Hn with rfl | ⟨h, -⟩
    all_goals try (exfalso; exact absurd h (by decide))
    all_goals repeat (first | wp_if_destruct | wp_auto | wp_load)
    all_goals try simp only
    all_goals
      wp_apply wp_fixTrailer _ ms $$ [Hh] as Hh
      · iframe; ipureintro; exact Htr
    all_goals repeat (first | iintro - | wp_if_destruct | wp_auto | wp_load)
    all_goals try simp only
    all_goals (iapply HΦ; iexists nb, _; iframe; ipureintro; cases rqv; rfl)

end proof

end net.http
end Perennial
