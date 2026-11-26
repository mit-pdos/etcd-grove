/-
**Proved** (dsv-retire-3 session 7, 2026-11-26, mit-pdos/etcd-grove#49 step 3; zerolog v1.23.0 now
translated with bodies): `(*Logger).Info()` is `l.newEvent(InfoLevel, nil)`, whose lemma
`wp_Logger_newEvent` (`LoggerNewEvent.lean`) gives the event's token, the defined `eventTok`
(`EventTok.lean`), over the statement of `(*Event).Str` (`Event.Str.spec`, passed by
`HypsHoldLinked.lean`). Its statement is unchanged. Until dsv-retire-3 a trust-boundary axiom, whose
header read:

**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `(*Logger).Info()` on a pointer `l ↦{dq} lg` (given back) to a logger made by `New(nil)` (`loggerOk lg`) returns an event (`nil` when the level is disabled) with its exclusive token `eventTok e` (the spec `Logger.level.spec` at `Info`: zerolog's `Info` is `l.newEvent(InfoLevel, nil)`, which reads the logger and, the level enabled, takes an `*Event` from the pool; a nil `l` panics, excluded by the points-to; dsv-fix6 added the points-to and `loggerOk`, a logger made by another path, or one being overwritten, having no spec: the dsv-fix4 review's second gap). Until dsv-fix4 a field of rabia's statement premise
`github_com.rs.zerolog.Hyps` (`Spec.lean`, whose header argues each spec of the real library;
the event token was then existential, `∃ ownEvent, EventSpecs ownEvent`, and is now the fixed
opaque `zerolog.eventTok`, `EventTok.lean`). Reviews: `notes/axiom-review/dsv-fix4/zerolog.md`, `notes/axiom-review/dsv-fix6/zerolog.md`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.LoggerNewEvent

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- `(*Logger).Info()` (the file header). -/
theorem github_com.rs.zerolog.Logger.Info.wp_proof
    (wp_Str : github_com.rs.zerolog.Event.Str.spec (GF := GF) github_com.rs.zerolog.eventTok) :
  github_com.rs.zerolog.Logger.level.spec (GF := GF) github_com.rs.zerolog.eventTok
    go!"Info" := by
  intro l lg dq
  wp_start as ⟨Hl, #Hok⟩
  unfold github_com.rs.zerolog.InfoLevel
  wp_auto
  wp_apply (github_com.rs.zerolog.wp_Logger_newEvent wp_Str l lg dq _
      (by simp [github_com.rs.zerolog.fiveLevels]) _ rfl) $$ [$Hl $Hok] as %e ⟨Hl, Htok⟩
  try wp_auto
  iapply HΦ
  iframe Hl Htok

end proof

end Perennial
