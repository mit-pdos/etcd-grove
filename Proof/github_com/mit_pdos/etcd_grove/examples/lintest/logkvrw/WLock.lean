/-
Lean-first (no Rocq counterpart).

# lintest/logkvrw: the write lock in the base's terms (2026-10-28)

The writers (`Put`, `applyLoop`) see `s.mu`'s write lock as the base saw its mutex: `Lock` gives
the whole lock invariant `logkvrwR` (under a later, which the next pure step takes off) with the
lock held (`wLocked`), `Unlock` takes them back, and `&s.mu` is a `Locker` with that resource,
for `Cond.Wait` (`wLocker`). From Perennial's guarded `RWMutex` (`wp_Lock_guard`,
`wp_Unlock_guard`): after `Lock`, the writer flips `γb` to `true` with `rdR 1`'s half and takes
the writer's part out of `wInv`; before `Unlock`, it puts it back and flips `γb` to `false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Defs
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Assumptions]

/-- `s.mu.Lock()`: the base's lock invariant, with the write lock held. -/
theorem wp_wLock (γ γr γb : GName) (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wLock γ γr γb s }}
      (App (Val (muAddr s @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); wLocked γ γb s ∗ ▷ logkvrwR γ γr s }} := by
  iintro %Φ ⟨#Hsync, #Hw⟩ HΦ
  iunfold wLock at Hw
  icases Hw with ⟨#Hg, #Hinv⟩
  iapply wp_fupd
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hl, HP⟩
  iunfold rdR at HP
  icases HP with >HP
  icases HP with ⟨%st, Hst, Hgst, Hb⟩
  iinv Hinv with Hi Hclose
  iunfold wInv at Hi
  icases Hi with (>Ht | ⟨>Hf, HW⟩)
  · icombine Hb Ht gives % ⟨_, Hbad⟩
    cases Hbad
  imod ghostVar_update_halves true γb _ _ $$ Hb Hf with ⟨Hb, Hf⟩
  imod Hclose $$ [Hf] with -
  · inext
    iunfold wInv
    ileft
    iexact Hf
  imodintro
  iapply HΦ
  isplitl [Hl Hb]
  · iunfold wLocked
    iframe
  inext
  iapply logkvrwR_join γ γr s st $$ [HW Hst Hgst]
  iframe

/-- `s.mu.Unlock()`: gives the base's lock invariant back with the write lock. -/
theorem wp_wUnlock (γ γr γb : GName) (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wLock γ γr γb s ∗ wLocked γ γb s ∗
        ▷ logkvrwR γ γr s }}
      (App (Val (muAddr s @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, #Hw, Hlk, HR⟩ HΦ
  iunfold wLock at Hw
  icases Hw with ⟨#Hg, #Hinv⟩
  iunfold wLocked at Hlk
  icases Hlk with ⟨Hl, Hb⟩
  ihave HR2 : ▷ (wrR γ γr s ∗ ∃ st : GoString, stateAddr s ↦ st ∗ ghostVar γ (1 : Qp).half st)
    $$ [HR]
  · inext
    iapply logkvrwR_split $$ HR
  icases HR2 with ⟨HW, Hst⟩
  iapply fupd_wp
  iinv Hinv with Hi Hclose
  iunfold wInv at Hi
  icases Hi with (>Ht | ⟨>Hf, _⟩)
  · imod ghostVar_update_halves false γb _ _ $$ Hb Ht with ⟨Hb, Ht⟩
    imod Hclose $$ [Ht HW] with -
    · inext
      iunfold wInv
      iright
      iframe
    imodintro
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hl Hst Hb]
    · inext
      iunfold rdR
      icases Hst with ⟨%st, Hst, Hgst⟩
      iexists st
      iframe
    iapply HΦ
    itrivial
  · icombine Hb Hf gives % ⟨_, Hbad⟩
    cases Hbad

/-- `&s.mu` is a `Locker` whose `Lock` gives the base's lock invariant with the write lock. -/
theorem wLocker (γ γr γb : GName) (s : Loc) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗ wLock γ γr γb s -∗
      sync.isLocker (muLocker s) iprop(wLocked γ γb s ∗ ▷ logkvrwR γ γr s) := by
  iintro #Hi #Hw
  unfold sync.isLocker
  isplitl
  · imodintro
    iintro %Φ _ HΦ
    wp_apply wp_wLock γ γr γb s $$ [$Hi $Hw] as H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hl, HR⟩ HΦ
    wp_apply wp_wUnlock γ γr γb s $$ [$Hi $Hw $Hl $HR]
    iapply HΦ
    itrivial

end proof

end logkvrw
end lintest
end EtcdGrove
end Perennial
