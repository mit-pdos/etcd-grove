/-
**Proved** (dsv-retire-3 session 6, 2026-11-26, mit-pdos/etcd-grove#49 step 3; zerolog v1.23.0 now
translated with bodies): `(*Event).Str(k, x)` returns its receiver with its token: on `nil` at once;
otherwise it appends the key (`internal/json`'s `AppendKey`, which reads the buffer's last byte: the
token's buffer is non-empty) and the value (`AppendString`) to the buffer it owns
(`internal/json/AppendString.lean`), over the defined `eventTok` (`EventTok.lean`) and Perennial's
`utf8.DecodeRuneInString` spec (passed by `HypsHoldLinked.lean`). Its statement is unchanged. Until
dsv-retire-3 a trust-boundary axiom, whose header read:

**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `(*Event).Str(k, x)`, with the event's token, returns its receiver with the token (the field `EventSpecs.Event_Str`: on a `nil` event it returns `nil` at once; otherwise it appends the key and the value to the event's buffer, which only the token's holder uses). Until dsv-fix4 a field of rabia's statement premise
`github_com.rs.zerolog.Hyps` (`Spec.lean`, whose header argues each spec of the real library;
the event token was then existential, `∃ ownEvent, EventSpecs ownEvent`, and is now the fixed
opaque `zerolog.eventTok`, `EventTok.lean`). Review: `notes/axiom-review/dsv-fix4/zerolog.md`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.EventTok
public import Dsverify.Proof.github_com.rs.zerolog.internal.json.AppendString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- `(*Event).Str` (the file header). -/
theorem github_com.rs.zerolog.Event.Str.wp_proof
    (wp_DecodeRuneInString : unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG)) :
  ∀ (e : Loc) (k : GoString) (x : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ github_com.rs.zerolog.eventTok e }}
      (App (App (Val (e @!! go.GoType.PointerType github_com.rs.zerolog.Event.ty @!! go!"Str")) (Val #k)) (Val #x))
    {{ RET #e; github_com.rs.zerolog.eventTok e }} := by
  intro e k x
  wp_start as Htok
  ihave #Hi := github_com.rs.zerolog.zerologInit_access $$ Hpkg
  unfold github_com.rs.zerolog.eventTok
  icases Htok with (%Hnull | ⟨%v, %bs, %w, He, Hb, Hcap, %Hne, #HD, %Hv⟩)
  · subst Hnull
    wp_auto
    iapply HΦ
    ileft
    ipureintro; rfl
  · icases typedPointsto_not_null_dup _ _ _ $$ He with ⟨He, %Hnn⟩
    wp_auto
    rw [decide_eq_false Hnn]
    unfold github_com.rs.zerolog.zerologInit
    icases Hi with ⟨-, -, -, #Henc, -, -⟩
    wp_auto
    wp_method_call
    try wp_auto
    wp_apply (github_com.rs.zerolog.internal.json.wp_AppendKey wp_DecodeRuneInString) $$ [$Hb $Hcap]
      as %d1 ⟨%q1, Hb, Hcap⟩
    · exact Hne
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply (github_com.rs.zerolog.internal.json.wp_AppendString wp_DecodeRuneInString) $$ [$Hb $Hcap]
      as %d2 ⟨%q2, Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iright
    iexists _, bs ++ q1 ++ q2, w
    iframe He Hb Hcap HD
    ipureintro
    exact ⟨by simp [Hne], Hv⟩

end proof

end Perennial
