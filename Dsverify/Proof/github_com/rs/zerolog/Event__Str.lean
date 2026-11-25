/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `(*Event).Str(k, x)`, with the event's token, returns its receiver with the token (the field `EventSpecs.Event_Str`: on a `nil` event it returns `nil` at once; otherwise it appends the key and the value to the event's buffer, which only the token's holder uses). Until dsv-fix4 a field of rabia's statement premise
`github_com.rs.zerolog.Hyps` (`Spec.lean`, whose header argues each spec of the real library;
the event token was then existential, `∃ ownEvent, EventSpecs ownEvent`, and is now the fixed
opaque `zerolog.eventTok`, `EventTok.lean`). Review: `notes/axiom-review/dsv-fix4/zerolog.md`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.EventTok

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.rs.zerolog.Event.Str.wp_proof :
  ∀ (e : Loc) (k : GoString) (x : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ github_com.rs.zerolog.eventTok e }}
      (App (App (Val (e @!! go.GoType.PointerType github_com.rs.zerolog.Event.ty @!! go!"Str")) (Val #k)) (Val #x))
    {{ RET #e; github_com.rs.zerolog.eventTok e }}

end ax

end Perennial
