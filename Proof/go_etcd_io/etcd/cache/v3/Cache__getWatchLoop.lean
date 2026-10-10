/-
Proof of `Spec/Cache__getWatchLoop.lean`. Lean-first (no Rocq counterpart).

The loop's invariant: the demux's writer, in any state, with the revision bound's authority, and
the wait-group token. Each `get` gets etcd's linearizability for the revision bound from the
client (`isEtcdKV`), knowing etcd has reached it (`cacheBound`).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatchLoop
public import Spec.go_etcd_io.etcd.cache.v3.defaultConfig
public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatch

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem Cache.getWatchLoop.wp_proof
    (wp_defaultConfig : defaultConfig.spec (GF := GF) (hG := hG))
    (wp_getWatch : Cache.getWatch.spec (GF := GF) (hG := hG)) :
    Cache.getWatchLoop.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap c0
  wp_start as ⟨#Hc, Hw, Hrun⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  icases HisICtx with ⟨%ics, #Hctxi, -⟩
  ihave #Hctxi' := Hctxi
  iNamed Hctxi'
  try wp_auto
  wp_apply wp_defaultConfig
  try ipersist c
  try ipersist ctx
  try ipersist backoff
  ihave HI : (∃ (c1 : DemuxCore), "Hw" ∷ cacheWriter cf γd cap c1 ∗
      "Hrun" ∷ cacheWgLoopRunning cf : IProp GF) $$ [Hw Hrun]
  · iexists c0; simp only [named]; iframe
  wp_for HI
  -- `ctx.Err()`
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_apply HErrU as %err -
  cases err with
  | ok e =>
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hrun
    iexists c1
    iframe
  | nil =>
  wp_auto
  -- `c.getWatch()`
  wp_apply wp_getWatch c cf γr γd cap c1 $$ [$Hpkg $Hc $Hw $Hrun]
    as %err ⟨%Hne, Hrun, %c2, Hw⟩
  obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
    cases err with
    | nil => exact absurd rfl Hne
    | ok e => exact ⟨e, rfl⟩
  wp_auto
  -- `fmt.Printf(...)`
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl -
  wp_apply fmt.wp_Printf $$ [$Hfmt] as %n %e2 -
  -- the backoff: `select` on `ctx.Done()` and `time.After(backoff)`
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto
  wp_apply +noauto time.wp_After as %tch %γt #Htch
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-ctx.Done()`: return
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hrun
    iexists c2
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-time.After(backoff)`: loop
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %t -
    wp_auto
    wp_for_post
    iframe HΦ
    iexists c2
    simp only [named]
    iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
