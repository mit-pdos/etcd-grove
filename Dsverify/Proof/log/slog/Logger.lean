/-
The proofs of `log/slog`'s specs (`Dsverify/Spec/log/slog/Logger.lean`) from the model's code
(`models/log/slog`, translated with its bodies): `New` at `DiscardHandler`'s value, the load of
`DiscardHandler`, a `DiscardHandler` logger's `Debug`/`Info`/`Warn`/`Error` (its `Enabled` is
false: `log` returns at once) and the package-level `Debug` (the default logger's `defaultHandler`
is enabled from `LevelInfo` up, so not at `LevelDebug`).
-/
module

public import Dsverify.Spec.log.slog.Logger

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace log.slog

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : log.slog.Assumptions]

theorem DiscardHandler.load_proof : DiscardHandler.load_spec (GF := GF) (hG := hG) := by
  wp_start as #Hinit
  ihave #Hst : pkgState (GF := GF) $$ []
  · iapply isPkgInit_access $$ Hinit
  iunfold pkgState at Hst
  icases Hst with ⟨#Hdh, -⟩
  wp_auto
  iapply HΦ
  itrivial

theorem New.wp_proof : New.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_auto
  iunfold isLogger
  iStructNamed «$r0»
  ipersist handler
  iapply HΦ
  iexact handler

theorem Logger.Debug.wp_proof : Logger.Debug.spec (GF := GF) (hG := hG) := by
  intro l msg arg xs dq
  wp_start as ⟨-, #Hl, Harg, -⟩
  iunfold isLogger at Hl
  wp_auto
  iapply HΦ
  iexact Harg

theorem Logger.Info.wp_proof : Logger.Info.spec (GF := GF) (hG := hG) := by
  intro l msg arg xs dq
  wp_start as ⟨-, #Hl, Harg, -⟩
  iunfold isLogger at Hl
  wp_auto
  iapply HΦ
  iexact Harg

theorem Logger.Warn.wp_proof : Logger.Warn.spec (GF := GF) (hG := hG) := by
  intro l msg arg xs dq
  wp_start as ⟨-, #Hl, Harg, -⟩
  iunfold isLogger at Hl
  wp_auto
  iapply HΦ
  iexact Harg

theorem Logger.Error.wp_proof : Logger.Error.spec (GF := GF) (hG := hG) := by
  intro l msg arg xs dq
  wp_start as ⟨-, #Hl, Harg, -⟩
  iunfold isLogger at Hl
  wp_auto
  iapply HΦ
  iexact Harg

theorem Debug.wp_proof : Debug.spec (GF := GF) (hG := hG) := by
  intro msg arg xs dq
  wp_start as ⟨#Hinit, Harg, -⟩
  ihave #Hst : pkgState (GF := GF) $$ []
  · iapply isPkgInit_access $$ Hinit
  iunfold pkgState at Hst
  icases Hst with ⟨-, %dl, #Hdl, #Hh⟩
  wp_auto
  iapply HΦ
  iexact Harg

end proof

end log.slog

end Perennial
