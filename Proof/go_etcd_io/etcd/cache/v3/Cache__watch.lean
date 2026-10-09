/-
Proof of `Spec/Cache__watch.lean`. Lean-first (no Rocq counterpart).

The loop's invariant: the demux's writer at a state `cc` whose stream continues the watch at
`rev - 1` (`CursorOk`, from `Init(rev)`: `initCore_ok`), and the store's writer at a synced state
whose latest map is etcd's state at `Y`, with `rev ≤ Y + 1` and `Y` at most the latest revision.
Each iteration's `applyErr` is a handoff channel (`Handoff.lean`): the goroutine sends
`applyStorage`'s error with the store's writer (`watchWs`), or closes it with the writer and its
certificate (`watchWc`); the loop takes them at its first receive, in `watchEvents` or in the
wait. It continues only after `nil` from both, so with `watchWc`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- What `applyErr` carries with a value: a non-nil error. -/
def watchP (v : GoError) : IProp GF := iprop(⌜v ≠ GoInterface.nil⌝)

/-- What `applyErr` hands over with a value (`applyStorage` failed): the store's writer. -/
def watchWs (cf : CacheFields) : IProp GF :=
  iprop(∃ st : StoreState, storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st)

/-- What `applyErr` hands over with a close that follows no value (`applyStorage` returned `nil`):
the store's writer, at a synced state whose latest map is etcd's state at `Y' ≥ Y`, at most the
latest revision. -/
def watchWc (cf : CacheFields) (Y : w64) : IProp GF :=
  iprop(∃ (st : StoreState) (Y' : w64), storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st ∗
    isEtcdKvs Y' cf.pfx st.latest ∗
    ⌜st.Synced ∧ sint.Z Y ≤ sint.Z Y' ∧ sint.Z Y' ≤ sint.Z st.latestRev⌝)

theorem Cache.watch.wp_proof
    (wp_Init : demux.Init.spec (GF := GF) (hG := hG))
    (wp_newWatcher : newWatcher.spec (GF := GF) (hG := hG))
    (wp_Register : demux.Register.spec (GF := GF) (hG := hG))
    (wp_applyStorage : Cache.applyStorage.spec (GF := GF) (hG := hG))
    (wp_watchEvents : Cache.watchEvents.spec (GF := GF) (hG := hG))
    (wp_Unregister : demux.Unregister.spec (GF := GF) (hG := hG)) :
    Cache.watch.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap rev R c0 st0
  wp_start as ⟨#Hc, Hw, Hwr, #HR, %Hpre⟩
  obtain ⟨hsync, hrev, hrevR, hRl⟩ := Hpre
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  wp_auto
  -- `c.demux.Init(rev)`
  unfold cacheWriter
  icases Hw with ⟨Hdw, %Hwo⟩
  icases demuxWriter_inv $$ Hdw with ⟨Hdw, %Hinv⟩
  wp_apply wp_Init cf.demux γd cap (etcdStepCert cf.pfx) c0 rev $$ [$Hpkg $HisDemux $Hdw] as Hdw
  have hi := initCore_ok cf.pfx cap c0 rev Hinv Hwo hrev
  -- `readyOnce := sync.Once{}`
  imod sync.init_Once readyOnce_ptr iprop(True) iprop(True) ⊤ $$ [$readyOnce] with #Honce
  ipersist c
  ipersist rev
  ihave HI : (∃ (cc : DemuxCore) (st : StoreState) (Y : w64),
      "Hw" ∷ cacheWriter cf γd cap cc ∗
      "Hwr" ∷ storeWriter cf.store cf.γs cf.scap (etcdCert cf.pfx) st ∗
      "#HY" ∷ isEtcdKvs Y cf.pfx st.latest ∗
      "%Hi" ∷ ⌜CursorOk cf.pfx cc (rev - W64 1) ∧ st.Synced ∧ sint.Z rev ≤ sint.Z Y + 1 ∧
        sint.Z Y ≤ sint.Z st.latestRev⌝ : IProp GF) $$ [Hdw Hwr]
  · iexists (initCore c0 rev).1, st0, R
    simp only [named]
    unfold cacheWriter
    iframe Hdw Hwr HR
    ipureintro; exact ⟨hi.2, hi.1, hsync, hrevR, hRl⟩
  wp_for HI
  obtain ⟨hcur, hsyncc, hrevY, hYl⟩ := Hi
  ihave #Hcfg' := Hcfg
  iStructNamedPrefix Hcfg' "Cfg"
  wp_auto
  wp_apply wp_newWatcher cf.cfg.PerWatcherBufferSize' func.nil none
    (demuxPub (etcdStepCert cf.pfx) none rev) as %w %γw ⟨#Hwi, Hwopen, Hwcons, Hwuniq⟩
  · isplitr
    · ipureintro; exact Hbuf
    isplitr
    · unfold keyPredOk; ipureintro; rfl
    imodintro
    unfold demuxPub
    iapply demuxPubBody_nil
  -- `c.demux.Register(storeW, rev)`, with the writer's demux token
  unfold cacheWriter demuxWriter
  icases Hw with ⟨⟨Hcore, Hh, %Hinvc⟩, %Hwoc⟩
  wp_apply wp_Register cf.demux γd cap (etcdStepCert cf.pfx) w γw none rev
    $$ [$Hpkg $HisDemux $Hh $Hwi $Hwopen $Hwuniq] as ⟨Hh, %sR, %M, Hreg, %HsR⟩
  -- `applyErr := make(chan error, 1)`, a handoff channel
  wp_apply chan.wp_make2 (V := GoError) (W64 1) as %ch %γch ⟨#Hch, %_, Hoc⟩
  · ipureintro; decide
  imod start_handoff ch watchP (watchWs cf) (watchWc cf Y) γch $$ Hch [Hoc]
    with ⟨%γa, %-, #Hae, Hprod, Hcons⟩
  · iexact Hoc
  ipersist storeW
  ipersist applyErr
  -- the goroutine: `applyStorage`, then the handoff
  wp_apply wp_fork $$ [Hwcons Hwr Hprod]
  · wp_auto
    wp_apply wp_applyStorage c cf γr γd cap w γw rev Y st $$ [$Hpkg $Hc $Hwi $Hwcons $Hwr $HY]
      as %err ⟨%st', Hwr, Hok⟩
    · ipureintro; exact ⟨hsyncc, hrev, hrevY, Or.inr hYl⟩
    cases err with
    | ok e =>
      wp_auto
      wp_apply wp_handoff_send γa ch watchP (watchWs cf) (watchWc cf Y) (GoInterface.ok e)
        $$ [$Hae $Hprod Hwr] as Hprod
      · unfold watchP watchWs
        isplitr
        · ipureintro; intro h; cases h
        iexists st'; iexact Hwr
      try wp_auto
      wp_apply wp_handoff_close γa ch watchP (watchWs cf) (watchWc cf Y) true $$ [$Hae $Hprod]
      · simp only [↓reduceIte]; itrivial
      itrivial
    | nil =>
      ihave Hok' := Hok $$ []
      · ipureintro; rfl
      wp_auto
      wp_apply wp_handoff_close γa ch watchP (watchWs cf) (watchWc cf Y) false
        $$ [$Hae $Hprod Hwr Hok']
      · simp only [Bool.false_eq_true, ↓reduceIte]
        unfold watchWc
        icases Hok' with ⟨%R', #HR', %Hp⟩
        iexists st', R'
        iframe Hwr HR'
        ipureintro; exact ⟨Hp.1, Hp.2.1, Hp.2.2 hYl⟩
      itrivial
  -- `err := c.watchEvents(rev, applyErr, &readyOnce)`
  try wp_auto
  wp_apply wp_watchEvents c cf γr γd cap rev ch γa watchP (watchWs cf) (watchWc cf Y)
    readyOnce_ptr cc $$ [$Hpkg $Hc $Hae $Hcons $Honce Hcore Hh] as %err ⟨%c1, Hw, %Hc1, Hres⟩
  · unfold cacheWriter demuxWriter
    iframe Hcore Hh
    ipureintro; exact ⟨⟨Hinvc, Hwoc⟩, hrev, hcur⟩
  -- `c.demux.Unregister(storeW)`
  unfold cacheWriter demuxWriter
  icases Hw with ⟨⟨Hcore, Hh, %Hinv1⟩, %Hwo1⟩
  wp_apply wp_Unregister cf.demux γd cap (etcdStepCert cf.pfx) w γw none sR
    $$ [$Hpkg $HisDemux $Hh $Hreg] as ⟨Hh, -⟩
  -- `applyStorageErr := <-applyErr`: the store's writer is back
  have hz : (zero_val GoError) = GoInterface.nil := rfl
  icases Hres with (Hcons | ⟨Hcons, Hgot⟩)
  · -- `watchEvents` took nothing
    wp_apply wp_handoff_receive γa ch watchP (watchWs cf) (watchWc cf Y) false
      $$ [$Hae $Hcons] as %v %ok ⟨-, Hgot⟩
    cases ok
    · -- the close: `nil`, and the writer with its certificate
      simp only [handoffGot, Bool.false_eq_true, ↓reduceIte]
      icases Hgot with ⟨%Hv, HWc⟩
      subst Hv
      unfold watchWc
      icases HWc with ⟨%st', %Y', Hwr, #HY', %Hp⟩
      cases err with
      | ok e =>
        wp_auto
        wp_for_post
        iapply HΦ
        isplitr
        · ipureintro; intro h; cases h
        iexists c1, st'
        iframe Hcore Hh Hwr
        ipureintro; exact ⟨Hinv1, Hwo1⟩
      | nil =>
        rw [hz]
        wp_auto
        wp_for_post
        iframe HΦ
        iexists c1, st', Y'
        simp only [named]
        iframe Hcore Hh Hwr HY'
        ipureintro; exact ⟨⟨Hinv1, Hwo1⟩, Hc1, Hp.1, by omega, Hp.2.2⟩
    · -- a value: `applyStorage`'s error, and the writer
      simp only [handoffGot, Bool.false_eq_true, ↓reduceIte]
      unfold watchP
      icases Hgot with ⟨%Hv, HWs⟩
      unfold watchWs
      icases HWs with ⟨%st', Hwr⟩
      obtain ⟨e', rfl⟩ : ∃ e', v = GoInterface.ok e' := by
        cases v with
        | nil => exact absurd rfl Hv
        | ok e' => exact ⟨e', rfl⟩
      cases err with
      | ok e =>
        wp_auto
        wp_for_post
        iapply HΦ
        isplitr
        · ipureintro; intro h; cases h
        iexists c1, st'
        iframe Hcore Hh Hwr
        ipureintro; exact ⟨Hinv1, Hwo1⟩
      | nil =>
        wp_auto
        wp_for_post
        iapply HΦ
        isplitr
        · ipureintro; intro h; cases h
        iexists c1, st'
        iframe Hcore Hh Hwr
        ipureintro; exact ⟨Hinv1, Hwo1⟩
  · -- `watchEvents` took it: the wait receives the close
    wp_apply wp_handoff_receive γa ch watchP (watchWs cf) (watchWc cf Y) true
      $$ [$Hae $Hcons] as %v %ok ⟨-, Hgot2⟩
    simp only [handoffGot, ↓reduceIte]
    icases Hgot2 with %Hv
    obtain ⟨rfl, rfl⟩ := Hv
    unfold watchP
    icases Hgot with (⟨%Herr, HWs⟩ | ⟨%Herr, HWc⟩)
    · -- `applyStorage`'s error, returned by `watchEvents`
      unfold watchWs
      icases HWs with ⟨%st', Hwr⟩
      obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
        cases err with
        | nil => exact absurd rfl Herr
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      wp_for_post
      iapply HΦ
      isplitr
      · ipureintro; intro h; cases h
      iexists c1, st'
      iframe Hcore Hh Hwr
      ipureintro; exact ⟨Hinv1, Hwo1⟩
    · -- the close, received by `watchEvents`: `nil`
      subst Herr
      unfold watchWc
      icases HWc with ⟨%st', %Y', Hwr, #HY', %Hp⟩
      rw [hz]
      wp_auto
      wp_for_post
      iframe HΦ
      iexists c1, st', Y'
      simp only [named]
      iframe Hcore Hh Hwr HY'
      ipureintro; exact ⟨⟨Hinv1, Hwo1⟩, Hc1, Hp.1, by omega, Hp.2.2⟩

end proof

end EtcdGrove
end Perennial
