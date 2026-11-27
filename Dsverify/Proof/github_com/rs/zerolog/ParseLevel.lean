/-
**Proved** (dsv-retire-3, 2026-11-26, mit-pdos/etcd-grove#49 step 3; zerolog v1.23.0 now translated
with bodies): `ParseLevel("warn")` returns `(WarnLevel, nil)`, from the translation and zerolog's fact (`zerologInit`, `Base.lean`). Its
statement is unchanged. Until dsv-retire-3 a trust-boundary axiom, whose header read:

**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `ParseLevel("warn")` returns `(WarnLevel, nil)`, `WarnLevel` = 2 (the field `Hyps.ParseLevel_warn`: zerolog's `ParseLevel` switches on the string). Until dsv-fix4 a field of rabia's statement premise
`github_com.rs.zerolog.Hyps` (`Spec.lean`, whose header argues each spec of the real library;
the event token was then existential, `∃ ownEvent, EventSpecs ownEvent`, and is now the fixed
opaque `zerolog.eventTok`, `EventTok.lean`). Review: `notes/axiom-review/dsv-fix4/zerolog.md`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- `ParseLevel("warn")`, from the translation: the switch compares `"warn"` with
`LevelFieldMarshalFunc` of `Trace`, `Debug`, `Info` and `Warn` (`marshalSpec`, zerolog's fact) and
returns at the fourth; `fmt.Errorf` is not reached. -/
theorem github_com.rs.zerolog.ParseLevel.wp_proofWarn :
    github_com.rs.zerolog.ParseLevel.warn.spec (GF := GF) := by
  wp_start as #Hpkg
  ihave #Hi := github_com.rs.zerolog.zerologInit_access $$ Hpkg
  unfold github_com.rs.zerolog.zerologInit
  icases Hi with ⟨-, -, ⟨%f, #HLf, #Hf⟩, -⟩
  unfold github_com.rs.zerolog.marshalSpec
  unfold github_com.rs.zerolog.TraceLevel github_com.rs.zerolog.DebugLevel
    github_com.rs.zerolog.InfoLevel github_com.rs.zerolog.WarnLevel
  wp_auto
  wp_apply Hf $$ []
  · ipureintro; simp [github_com.rs.zerolog.fiveLevels]
  try simp (config := { decide := true }) only [github_com.rs.zerolog.levelString]
  try wp_auto
  wp_apply Hf $$ []
  · ipureintro; simp [github_com.rs.zerolog.fiveLevels]
  try simp (config := { decide := true }) only [github_com.rs.zerolog.levelString]
  try wp_auto
  wp_apply Hf $$ []
  · ipureintro; simp [github_com.rs.zerolog.fiveLevels]
  try simp (config := { decide := true }) only [github_com.rs.zerolog.levelString]
  try wp_auto
  wp_apply Hf $$ []
  · ipureintro; simp [github_com.rs.zerolog.fiveLevels]
  try simp (config := { decide := true }) only [github_com.rs.zerolog.levelString]
  try wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
