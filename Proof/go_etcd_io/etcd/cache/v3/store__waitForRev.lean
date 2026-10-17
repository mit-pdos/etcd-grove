/-
Proof of `Spec/store__waitForRev.lean` (etcd-io/etcd#21600). Lean-first (no Rocq counterpart).

As `Cache.waitTillRevision`: the wait is `revCond.Wait()` under `s.mu.RLock()`, whose locker is
`s.mu.RLocker()` (Perennial's `Cond.wp_Wait_with` with `sync.rlocker_isLockerWith`); the wakeup is
`context.AfterFunc(ctx, s.revCond.Broadcast)` (`Spec/context/AfterFunc.lean`), whose callback
needs only `isCond`.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.store__waitForRev
public import Spec.context.AfterFunc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem store.waitForRev.wp_proof
    (wp_AfterFunc : context.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_Err : context.Err.spec (GF := GF) (hG := hG)) :
    store.waitForRev.spec (GF := GF) (hG := hG) := by
  intro s γ cap E R ctx cs rev
  wp_start as ⟨#Hs, Hrd, #Hctx⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hs' := Hs
  iunfold isStore at Hs'
  iNamed Hs'
  -- `s.mu.RLock()`
  iunfold storeReader at Hrd
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  ihave #Hlocker := sync.rlocker_isLockerWith (storeMuAddr s)
    (storeLockInv s γ cap E R) $$ Hsync
  wp_auto
  -- `stop := context.AfterFunc(ctx, s.revCond.Broadcast)`
  wp_apply wp_AfterFunc ctx cs $$ [$Hcpkg $Hctx] as %stop #Hstop
  · imodintro
    wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
    itrivial
  ihave #HErr := wp_Err ctx cs Broadcast.Unknown $$ Hctx
  ihave #HErrD := wp_Err ctx cs Broadcast.Done $$ Hctx
  wp_for_core
  wp_auto_lc 1
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  iunfold storeLockInv at HP
  iNamed HP
  wp_auto
  wp_if_destruct
  · -- `latest.rev < rev`: `revCond.Wait()`, then `ctx.Err()`
    wp_apply +noauto sync.Cond.wp_Wait_with _ (sync.rlockerOf (storeMuAddr s))
      (sync.ownRWMutex (storeMuAddr s) (storeLockInv s γ cap E R))
      iprop(sync.ownRWMutexRLocked (storeMuAddr s) (storeLockInv s γ cap E R) ∗
        ▷ storeLockInv s γ cap E R sync.rfrac)
      $$ [$Hcond $Hlocker Hrl Hst Hrev HlatestRev Hhist Hrest] as ⟨Hrl, HP⟩
    · iframe Hrl
      inext; iunfold storeLockInv; iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
    wp_auto
    wp_apply HErr as %err herr -
    cases err with
    | ok e =>
      rw [ite_eq_right (show GoInterface.ok e ≠ GoInterface.nil by intro h; cases h)]
      icases herr with ⟨#HPD, #Hcl⟩
      wp_auto
      wp_apply HErrD $$ [] as %err' %herr' #HerrS
      · iexact Hcl
      wp_for_post
      wp_apply Hstop as %b
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hrd
      · inext; iexact HP
      iapply HΦ
      isplitl [Hrd]
      · iunfold storeReader; iexact Hrd
      iright
      iframe HPD Hcl HerrS
      ipureintro; exact herr'
    | nil =>
      wp_auto
      wp_for_post
      iframe
  · -- caught up
    have hnlt : ¬ sint.Z st.latestRev < sint.Z rev := by
      intro h; apply Hif; rw [decide_eq_true h]
    rw [decide_eq_false hnlt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ihave #Hlbl := monoNatLbOwn_get $$ Hrev
    wp_auto
    wp_apply Hstop as %b
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist Hrest] as Hrd
    · inext; iunfold storeLockInv; iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
    iapply HΦ
    isplitl [Hrd]
    · iunfold storeReader; iexact Hrd
    ileft
    isplitr
    · ipureintro; rfl
    unfold storeRevLb
    iapply monoNatLbOwn_le (sint.nat rev)
      (by have h : sint.Z rev ≤ sint.Z st.latestRev := by omega
          first | exact Int.toNat_le_toNat h | word) $$ Hlbl

end proof

end EtcdGrove
end Perennial
