/-
**Proved** (dsv-retire-3, 2026-11-26, mit-pdos/etcd-grove#49 step 3; zerolog v1.23.0 now translated
with bodies): `SetGlobalLevel(l)` returns, from the translation and zerolog's fact (`zerologInit`, `Base.lean`). Its
statement is unchanged. Until dsv-retire-3 a trust-boundary axiom, whose header read:

**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; zerolog v1.23.0, translated names
only in the part): `SetGlobalLevel(l)` returns (the field `Hyps.SetGlobalLevel`: an atomic store of the level into the package variable `gLevel`). Until dsv-fix4 a field of rabia's statement premise
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

/-- `SetGlobalLevel(l)`, from the translation: an atomic store into `gLevel`'s cell, through the
invariant of zerolog's fact. -/
theorem github_com.rs.zerolog.SetGlobalLevel.wp_proof :
    github_com.rs.zerolog.SetGlobalLevel.spec (GF := GF) := by
  intro lv
  wp_start as #Hpkg
  ihave #Hi := github_com.rs.zerolog.zerologInit_access $$ Hpkg
  unfold github_com.rs.zerolog.zerologInit
  icases Hi with ⟨⟨%p, #HgL, #Ig⟩, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_StoreInt32 $$ [] [HΦ]
  · iPkgInit
  iinv Ig with ⟨%v, >Hv⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hmask
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
