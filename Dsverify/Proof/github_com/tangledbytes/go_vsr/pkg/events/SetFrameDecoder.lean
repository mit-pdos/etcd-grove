/-
`events.SetFrameDecoder(f)` (the lab's `Proof/events/SetFrameDecoder.lean`, D11; notes/dsv-vr.md):
under the hook's lock (`hookKnown`, events' package fact) it stores `f` if the hook is unset. For
now its postcondition is `True` (the lab's `frameDecoderSet` comes with the hook's full invariant).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Init
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.tangledbytes.go_vsr.pkg.events

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tangledbytes.go_vsr.pkg.events.Assumptions]

set_option goose.wp.extras true

theorem wp_SetFrameDecoder (f : GoFunc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events }}
      (App (Val (@! SetFrameDecoder)) (Val #f))
    {{ RET #(); True }} := by
  wp_start
  ihave #Hk : (hookKnown : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold hookKnown at Hk
  icases Hk with ⟨%mu, #Hmu, #Hlock⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock mu (hookLockInv (GF := GF)) $$ [$Hlock] as ⟨Hlocked, HR⟩
  iunfold hookLockInv at HR
  icases HR with ⟨%g, Hg⟩
  wp_auto
  wp_if_destruct
  all_goals
    wp_apply sync.Mutex.wp_Unlock mu (hookLockInv (GF := GF)) $$ [$Hlock $Hlocked Hg]
    · iunfold hookLockInv; iexists _; iframe
    iapply HΦ
    itrivial

end proof

end github_com.tangledbytes.go_vsr.pkg.events
end Perennial
