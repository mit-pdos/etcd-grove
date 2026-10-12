/-
Proof of `Spec/Cache__waitTillRevision.lean`. Lean-first (no Rocq counterpart).

The wait is `revCond.Wait()` under `s.mu.RLock()`, where `revCond`'s locker is
`s.mu.RLocker()`: Perennial's `Cond.wp_Wait_with` with `sync.rlocker_isLockerWith` (the
locker's `Lock` needs the reader token, which its `Unlock` gives back).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__waitTillRevision
public import Spec.go_etcd_io.etcd.cache.v3.store__LatestRev
public import Spec.go_etcd_io.etcd.cache.v3.conditionalProgressRequestor__add
public import Spec.go_etcd_io.etcd.cache.v3.conditionalProgressRequestor__remove

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

-- `wp_load` from a persistent struct points-to: the field-store `AccessStrict` instance
-- (which needs `DFrac.own 1`) is found first and the search does not backtrack.
attribute [-instance] Config.Config_access_store_WaitTimeout

theorem Cache.waitTillRevision.wp_proof
    (wp_LatestRev : store.LatestRev.spec (GF := GF) (hG := hG))
    (wp_add : conditionalProgressRequestor.add.spec (GF := GF) (hG := hG))
    (wp_remove : conditionalProgressRequestor.remove.spec (GF := GF) (hG := hG)) :
    Cache.waitTillRevision.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap ctx s rev
  wp_start as ⟨#Hc, #Hctx, Hrd⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isCacheFields
  iNamed Hc
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, -, ⟨%eCT, #HeCT⟩, -⟩
  ihave #HisStore' := HisStore
  iunfold isStore at HisStore'
  iNamed HisStore'
  ihave #Hctx' := Hctx
  iNamed Hctx'
  imod monoNatLbOwn_0 (GF := GF) cf.γs.rev with #Hlb0
  wp_auto
  unfold cacheReader
  wp_apply wp_LatestRev cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf) (W64 0) $$ [$HisStore $Hrd]
    as %lr ⟨Hrd, %st, #Hseen, #-, %Hlr⟩
  · unfold storeRevLb; rw [show sint.nat (W64 0) = 0 from rfl]; iexact Hlb0
  iunfold storeSeen at Hseen
  icases Hseen with ⟨%Hst, #Hlbst⟩
  subst Hlr
  wp_if_destruct
  · -- the store has caught up
    iapply HΦ
    iframe Hrd
    unfold waitResult
    ileft
    isplitr
    · ipureintro; rfl
    unfold storeRevLb
    iapply monoNatLbOwn_le (sint.nat rev) (by first | exact Int.toNat_le_toNat Hif | word) $$ Hlbst
  wp_apply wp_add cf.pr $$ [$HisPR]
  wp_apply time.wp_Now as %t0 -
  ihave #Hcfg' := Hcfg
  iStructNamedPrefix Hcfg' "Cfg"
  wp_apply time.wp_After as %tch %γt #Htch
  ipersist c
  ipersist ctx
  ipersist timeoutCh
  wp_apply wp_fork $$ []
  · -- the goroutine: broadcast on `revCond` at the timeout or when the context is done
    wp_auto
    wp_apply +noauto HDone as %ch1 %γ1 #Hdone
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Htch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
      inext
      iintro %t -
      wp_auto
      wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone
      iintro -
      wp_auto
      wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  -- `s.mu.RLock()`
  iunfold storeReader at Hrd
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  ihave #Hlocker := sync.rlocker_isLockerWith (storeMuAddr cf.store)
    (storeLockInv cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf)) $$ Hsync
  wp_auto
  -- the loop invariant: the context (`HP : ▷ P rfrac` from `RLock` and from `Wait`)
  wp_for_core
  wp_auto_lc 1
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  iunfold storeLockInv at HP
  iNamed HP
  wp_auto
  wp_if_destruct
  · -- `latest.rev < rev`
    wp_apply time.wp_Since as %d -
    wp_if_destruct
    · -- timed out: `ErrCacheTimeout`
      wp_for_post
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist Hrest] as Hrd
      · inext; iunfold storeLockInv; iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
      wp_apply wp_remove cf.pr $$ [$HisPR]
      iapply HΦ
      isplitl [Hrd]
      · iunfold storeReader; iexact Hrd
      unfold waitResult
      iright; ileft
      iexact HeCT
    -- `ctx.Err()`
    ihave #HErrU := HErr $$ %Broadcast.Unknown
    wp_apply HErrU $$ [] as %err herr
    cases err with
    | ok e =>
      -- the context is done: return `ctx.Err()`
      rw [ite_eq_right (show GoInterface.ok e ≠ GoInterface.nil by intro h; cases h)]
      icases herr with ⟨#HPD, #Hcl⟩
      wp_auto
      ihave #HErrD := HErr $$ %Broadcast.Done
      wp_apply HErrD $$ [] as %err' %herr'
      · iexact Hcl
      wp_for_post
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist Hrest] as Hrd
      · inext; iunfold storeLockInv; iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
      wp_apply wp_remove cf.pr $$ [$HisPR]
      iapply HΦ
      isplitl [Hrd]
      · iunfold storeReader; iexact Hrd
      unfold waitResult
      iright; iright
      iframe HPD Hcl
      ipureintro; exact herr'
    | nil =>
      wp_auto
      -- `revCond.Wait()`
      wp_apply +noauto sync.Cond.wp_Wait_with _ (sync.rlockerOf (storeMuAddr cf.store))
        (sync.ownRWMutex (storeMuAddr cf.store) (storeLockInv cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf)))
        iprop(sync.ownRWMutexRLocked (storeMuAddr cf.store)
          (storeLockInv cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf)) ∗
          ▷ storeLockInv cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf) sync.rfrac)
        $$ [$Hcond $Hlocker Hrl Hst Hrev HlatestRev Hhist Hrest] as ⟨Hrl, HP⟩
      · iframe Hrl
        inext; iunfold storeLockInv; iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
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
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist Hrest] as Hrd
    · inext; iunfold storeLockInv; iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
    wp_apply wp_remove cf.pr $$ [$HisPR]
    iapply HΦ
    isplitl [Hrd]
    · iunfold storeReader; iexact Hrd
    unfold waitResult
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
