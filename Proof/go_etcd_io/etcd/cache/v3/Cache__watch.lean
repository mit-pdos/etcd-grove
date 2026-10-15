/-
Proof of `Spec/Cache__watch.lean`. Lean-first (no Rocq counterpart).

The loop's invariant: the demux's writer at a state `cc` whose stream continues the watch at
`rev - 1` (`CursorOk`, from `Init(rev)`: `initCore_ok`), with the revision bound's authority, and
the wait-group token. The store needs nothing from the loop: each iteration's goroutine applies
its watcher's responses as one of the store's writers (`applyStorage`, which needs only the
store's newest snapshot at least `rev - 1`, persistent), runs in the wait group (`Add(1)` from a
running goroutine, `wp_cacheWg_AddRunning`; deferred `Done`), and may outlive the iteration: the
loop does not wait for it. `applyErr` is a handoff channel (`Handoff.lean`) that carries no
resource: `watchEvents` may take the goroutine's error or close; otherwise nobody reads it.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__watch
public import Spec.go_etcd_io.etcd.cache.v3.demux__Init
public import Spec.go_etcd_io.etcd.cache.v3.newWatcher
public import Spec.go_etcd_io.etcd.cache.v3.demux__Register
public import Spec.go_etcd_io.etcd.cache.v3.demux__Unregister
public import Spec.go_etcd_io.etcd.cache.v3.Cache__applyStorage
public import Spec.go_etcd_io.etcd.cache.v3.Cache__watchEvents

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- What `applyErr` carries with a value: a non-nil error, whose `Error()` returns some string. -/
def watchP (v : GoError) : IProp GF := iprop(⌜v ≠ GoInterface.nil⌝ ∗ errStrOk v)

theorem Cache.watch.wp_proof
    (wp_Init : demux.Init.spec (GF := GF) (hG := hG))
    (wp_newWatcher : newWatcher.spec (GF := GF) (hG := hG))
    (wp_Register : demux.Register.spec (GF := GF) (hG := hG))
    (wp_applyStorage : Cache.applyStorage.spec (GF := GF) (hG := hG))
    (wp_watchEvents : Cache.watchEvents.spec (GF := GF) (hG := hG))
    (wp_Unregister : demux.Unregister.spec (GF := GF) (hG := hG)) :
    Cache.watch.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap rev R c0
  wp_start as ⟨#Hc, Hw, Hrun, #HslbR, %Hpre⟩
  obtain ⟨hrev, hrevR⟩ := Hpre
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  ihave #Hslb : storeSnapLb cf.γs (rev - W64 1) $$ []
  · iapply storeSnapLb_mono cf.γs R (rev - W64 1) (by word) $$ HslbR
  wp_auto
  -- `c.demux.Init(rev)`
  unfold cacheWriter
  icases Hw with ⟨Hdw, #Hwo, Hbd⟩
  icases demuxWriter_inv $$ Hdw with ⟨Hdw, %Hinv⟩
  wp_apply wp_Init cf.demux γd cap (cacheCert cf) c0 rev $$ [$Hpkg $HisDemux $Hdw] as Hdw
  ihave Hi0 := initCore_ok cf.pfx cap c0 rev Hinv hrev $$ Hwo
  icases Hi0 with ⟨#Hic, #Hiw⟩
  -- `readyOnce := sync.Once{}`
  imod sync.init_Once readyOnce_ptr iprop(True) iprop(True) ⊤ $$ [$readyOnce] with #Honce
  ipersist c
  ipersist rev
  ihave HI : (∃ (cc : DemuxCore),
      "Hw" ∷ (demuxWriter cf.demux γd cap (cacheCert cf) cc ∗ WriterOk cf.pfx cc ∗
        ∃ B : w64, cacheBound cf B) ∗
      "Hrun" ∷ cacheWgLoopRunning cf ∗
      "#Hi" ∷ CursorOk cf.pfx cc (rev - W64 1) : IProp GF) $$ [Hdw Hbd Hrun]
  · iexists (initCore c0 rev).1
    simp only [named]
    iframe Hdw Hbd Hrun
    iframe Hiw Hic
  wp_for HI
  ihave #Hcfg' := Hcfg
  iStructNamedPrefix Hcfg' "Cfg"
  wp_auto
  wp_apply wp_newWatcher cf.cfg.PerWatcherBufferSize' func.nil none
    (demuxPub (cacheCert cf) none rev) as %w %γw ⟨#Hwi, Hwopen, Hwcons, Hwuniq⟩
  · isplitr
    · ipureintro; exact Hbuf
    isplitr
    · unfold keyPredOk; ipureintro; rfl
    imodintro
    unfold demuxPub
    iapply demuxPubBody_nil
  -- `c.demux.Register(storeW, rev)`, with the writer's demux token
  unfold demuxWriter
  icases Hw with ⟨⟨Hcore, Hh, %Hinvc⟩, #Hwoc, Hbd⟩
  wp_apply wp_Register cf.demux γd cap (cacheCert cf) w γw none rev
    $$ [$Hpkg $HisDemux $Hh $Hwi $Hwopen $Hwuniq] as ⟨Hh, %sR, %M, Hreg, %HsR⟩
  -- `applyErr := make(chan error, 1)`, a handoff channel carrying no resource
  wp_apply chan.wp_make2 (V := GoError) (W64 1) as %ch %γch ⟨#Hch, %_, Hoc⟩
  · ipureintro; decide
  imod start_handoff ch watchP iprop(True) iprop(True) γch $$ Hch [Hoc]
    with ⟨%γa, %-, #Hae, Hprod, Hcons⟩
  · iexact Hoc
  ipersist storeW
  ipersist applyErr
  -- `c.waitGroup.Add(1)`, by this running goroutine, depositing its thread token
  iunfold cacheWgLoopRunning at Hrun
  icases Hrun with ⟨Hown, Htok⟩
  wp_apply wp_cacheWg_AddRunning c cf Hthreads $$ [$Hsync $HisWg $HwgInv $Hown $Htok]
    as ⟨Hown, Hrun'⟩
  -- the goroutine: `defer c.waitGroup.Done()`, `applyStorage`, then the handoff; it exits with
  -- the thread token its `Done` returns, and the loop gets a fresh one
  wp_apply wp_fork_tok_self $$ [Hwcons Hprod Hrun']
  · wp_apply wp_with_defer as %defer defer
    try wp_auto
    wp_apply wp_applyStorage c cf γr γd cap w γw rev $$ [$Hpkg $Hc $Hwi $Hwcons $Hslb] as %err #HaS
    · ipureintro; exact hrev
    cases err with
    | ok e =>
      wp_auto
      wp_apply wp_handoff_send γa ch watchP iprop(True) iprop(True) (GoInterface.ok e)
        $$ [$Hae $Hprod] as Hprod
      · unfold watchP
        isplitl
        · isplitl []
          · ipureintro; intro h; cases h
          iexact HaS
        itrivial
      try wp_auto
      wp_apply wp_handoff_close γa ch watchP iprop(True) iprop(True) true $$ [$Hae $Hprod]
      · simp only [↓reduceIte]; itrivial
      try wp_auto
      wp_apply wp_cacheWg_Done c cf $$ [$Hsync $HisWg $HwgInv $Hrun'] as Htok
      iexact Htok
    | nil =>
      wp_auto
      wp_apply wp_handoff_close γa ch watchP iprop(True) iprop(True) false $$ [$Hae $Hprod]
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      try wp_auto
      wp_apply wp_cacheWg_Done c cf $$ [$Hsync $HisWg $HwgInv $Hrun'] as Htok
      iexact Htok
  iintro Htok
  ihave Hrun : cacheWgLoopRunning (GF := GF) cf $$ [Hown Htok]
  · unfold cacheWgLoopRunning; iframe
  -- `err := c.watchEvents(rev, applyErr, &readyOnce)`
  try wp_auto
  wp_apply wp_watchEvents c cf γr γd cap rev ch γa watchP iprop(True) iprop(True)
    readyOnce_ptr cc $$ [$Hpkg $Hc $Hae $Hcons $Honce Hcore Hh Hbd] as %err ⟨%c1, Hw, #Hc1, Hho⟩
  · unfold cacheWriter demuxWriter
    iframe Hcore Hh Hbd
    iframe Hwoc Hi
    isplitr
    · ipureintro; exact Hinvc
    ipureintro; exact hrev
  ihave #HeW : errStrOk err $$ [Hho]
  · iunfold watchP at Hho
    icases Hho with (⟨-, #H⟩ | ⟨-, (⟨⟨-, #H⟩, -⟩ | ⟨%Hn, -⟩)⟩)
    · iexact H
    · iexact H
    · subst Hn; iapply errStrOk_nil
  -- `c.demux.Unregister(storeW)`
  unfold cacheWriter demuxWriter
  icases Hw with ⟨⟨Hcore, Hh, %Hinv1⟩, #Hwo1, Hbd⟩
  wp_apply wp_Unregister cf.demux γd cap (cacheCert cf) w γw none sR
    $$ [$Hpkg $HisDemux $Hh $Hreg] as ⟨Hh, -⟩
  cases err with
  | ok e =>
    -- an error: return it
    wp_auto
    wp_for_post
    iapply HΦ
    isplitr
    · ipureintro; intro h; cases h
    iframe HeW
    iframe Hrun
    iexists c1
    iframe Hcore Hh Hbd
    iframe Hwo1
    ipureintro; exact Hinv1
  | nil =>
    -- `nil`: the next iteration, from `rev` again
    wp_auto
    wp_for_post
    iframe HΦ
    iexists c1
    simp only [named]
    iframe Hcore Hh Hbd Hrun
    iframe Hwo1 Hc1
    ipureintro; exact Hinv1

end proof

end EtcdGrove
end Perennial
