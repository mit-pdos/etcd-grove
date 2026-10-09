/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/Cache__Close.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.waitGroup.Wait()`, by its registered waiter: returns once the counter is zero. -/
theorem wp_cacheWg_Wait (c : Loc) (cf : CacheFields) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (cacheWgAddr c) cf.γwg cacheWgWGN ∗
        inv cacheWgN (cacheWgInv cf) ∗ sync.ownWaitGroupWaitToken cf.γwg }}
      (App (Val (cacheWgAddr c @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); sync.ownWaitGroupWaitToken cf.γwg }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Htok⟩ HΦ
  iapply sync.WaitGroup.wp_Wait (cacheWgAddr c) cf.γwg cacheWgWGN $$ [Htok] [HΦ]
  · iframe #
    iframe
  iinv Hinv with >Hi Hclose
  · exact sync.wg_mask_ndot_ne nroot "cacheWgCounter" "cacheWaitGroup" (by decide)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold cacheWgInv at Hi
  icases Hi with ⟨%ctr, %wn, Hwgo, Hwt, Hrun, Hbud, Hbauth, %Hctr, Hwn⟩
  iexists ctr
  iframe Hwgo
  iintro %H0 Hwgo
  imod Hmask with -
  imod Hclose $$ [Hwgo Hwt Hrun Hbud Hbauth Hwn] with -
  · unfold cacheWgInv
    iexists ctr, wn
    iframe
    ipureintro; exact Hctr
  imodintro
  iintro Htok
  iapply HΦ $$ Htok

theorem Cache.Close.wp_proof : Cache.Close.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap
  wp_start as ⟨#Hc, Hopen⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isCacheFields at Hc
  iNamed Hc
  wp_auto
  -- `c.stop()`
  wp_apply HisStop $$ []
  · imodintro; itrivial
  -- register as the wait group's waiter, depositing the "open" token
  iapply fupd_wp
  iinv HwgInv with >Hi Hclose
  iunfold cacheWgInv at Hi
  icases Hi with ⟨%ctr, %wn, Hwgo, Hwt, Hrun, Hbud, Hbauth, %Hctr, Hwn⟩
  icases Hwn with (%Hw0 | ⟨-, Hop1⟩)
  rotate_left
  · iexfalso
    iapply cacheOpen_excl cf 1 $$ [$Hopen $Hop1]
  subst Hw0
  imod fupd_mask_subseteq cacheWg_mask with Hmask
  imod sync.alloc_wait_token (cacheWgAddr c) cf.γwg cacheWgWGN 0 (by decide) $$ HisWg Hwt
    with ⟨Hwt, Htok⟩
  imod Hmask with -
  imod Hclose $$ [Hwgo Hwt Hrun Hbud Hbauth Hopen] with -
  · inext
    unfold cacheWgInv
    iexists ctr, 1
    iframe
    isplitr
    · ipureintro; exact Hctr
    iright
    iframe
    ipureintro; rfl
  imodintro
  -- `c.waitGroup.Wait()`
  wp_apply +noauto wp_cacheWg_Wait c cf $$ [$Hsync $HisWg $HwgInv $Htok] as Htok
  -- deregister, taking the "open" token back
  iapply fupd_wp
  iinv HwgInv with >Hi Hclose
  iunfold cacheWgInv at Hi
  icases Hi with ⟨%ctr, %wn, Hwgo, Hwt, Hrun, Hbud, Hbauth, %Hctr, Hwn⟩
  icases Hwn with (%Hw0 | ⟨%Hw1, Hopen⟩)
  · subst Hw0
    iexfalso
    iapply sync.waiters_none_token_false cf.γwg $$ Hwt Htok
  subst Hw1
  imod fupd_mask_subseteq cacheWg_mask with Hmask
  imod sync.dealloc_wait_token (cacheWgAddr c) cf.γwg cacheWgWGN 1 (by decide) $$ HisWg Hwt Htok
    with Hwt
  imod Hmask with -
  imod Hclose $$ [Hwgo Hwt Hrun Hbud Hbauth] with -
  · inext
    unfold cacheWgInv
    iexists ctr, 0
    iframe
    isplitr
    · ipureintro; exact Hctr
    ileft; ipureintro; rfl
  imodintro
  wp_auto
  iapply HΦ $$ Hopen

end proof

end EtcdGrove
end Perennial
