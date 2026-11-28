/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watcher__createWatchChan.lean` (k8s 7f-5b). The names
`kCancelPD` reads (`stop`, `prodEx`, `procEx`) are allocated before `WithCancel` (its `PDone'`), the
rest after it (`kWatch_alloc`, with `wc.ctx`'s Done name); `wc.ctx`'s `Err()` is a client error by the
client watcher's facts (`clientWatchOk_ctxErr`), its outgoing metadata its parent's. An empty predicate
is replaced by `storage.Everything` (`everything_selPredOkW`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watcher__createWatchChan
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.newBlockLogger
public import Spec.k8s_io.utils.clock.RealClock__Now
public import Proof.context.LibKeysChain
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]


set_option maxHeartbeats 1600000 in
theorem watcher.createWatchChan.wp_proof
    (wp_ShardingEnabled : storage.SelectionPredicate.ShardingEnabled.spec (GF := GF) (hG := hG))
    (wp_labelFieldEmpty : storage.SelectionPredicate.labelFieldEmpty.spec (GF := GF) (hG := hG))
    (wp_newBlockLogger : newBlockLogger.spec (GF := GF) (hG := hG))
    (wp_Now : clock.RealClock.Now.spec (GF := GF) (hG := hG)) :
    watcher.createWatchChan.spec (GF := GF) (hG := hG) := by
  intro _ Obj _ _ wp sp c W γk ci cd kp rev recur pred sel emp m Q Hpfx Hkp Hklen
  wp_start as ⟨#Hst, #Hsw, #Hwp, #Hctx, #Hmd, #Hsel⟩
  ihave #Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hco, -⟩
  iunfold contractOk at Hco
  icases Hco with ⟨-, -, #Hver, #Htr, -, -, -⟩
  ihave #Hsw' := Hsw
  iunfold storeWatchOk at Hsw'
  icases Hsw' with ⟨%wp', %nf, %crv, %rse, #Hsw2, -, -, -, #Hwgr, -, -, -, #Hwrse, -, -, #Hrse, #Hcw, -,
    %ot, #Hwot⟩
  ihave %Hwp := typedPointsto_agree_wand _ _ _ _ _ $$ Hwp Hsw2
  subst Hwp
  wp_auto
  wp_apply chan.wp_make2 (V := Loc) (W64 100) as %chI %γcI ⟨#HcI, %HcapI, HoI⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply chan.wp_make2 (V := k8s_io.apimachinery.pkg.watch.Event) (W64 100)
    as %chR %γcR ⟨#HcR, %HcapR, HoR⟩
  · ipureintro; decide
  (try wp_auto)
  iStructNamed «$r0»
  ihave #Hsel' := Hsel
  iunfold selPredOk at Hsel'
  icases Hsel' with ⟨%Hsp, -, #HE⟩
  wp_bind (App (Val (pred_ptr @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
    @!! go!"Empty")) (Val #()))
  iapply HE $$ pred
  inext
  iintro pred
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pclk : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock $$ []
  · iPkgInit
  ihave #Psto : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave #Hclk : clockNowOk (GF := GF) ⟨k8s_io.utils.clock.RealClock.ty,
      #(k8s_io.utils.clock.RealClock.mk : k8s_io.utils.clock.RealClock)⟩ $$ []
  · unfold clockNowOk
    iintro !> %Φ' HΦ'
    iapply (wp_Now _) $$ [$Pclk]
    inext
    iintro %t -
    iapply HΦ'
  cases emp
  · ihave #HselW := selPredOk_W c.S pred sel false $$ Hsel
    (try wp_auto)
    imod dghostVar_alloc (GF := GF) false with ⟨%gstop, Hstop⟩
    imod dghostVar_alloc (GF := GF) false with ⟨%gprodEx, HprodEx⟩
    imod dghostVar_alloc (GF := GF) false with ⟨%gprocEx, HprocEx⟩
    wp_apply (context.wp_WithCancel_ctx ci cd
      (kCancelPD (GF := GF) ⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx,
        gprocEx, ⟨gstop, gstop⟩⟩ cd)) $$ [] as %ctx' %γ' %cf ⟨#Hcs, #Hctx', -, #Hvf⟩
    · iframe #
    imod kWatch_alloc c W
      ⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx, gprocEx, γ'⟩
      cd sel false (kInScope kp recur) m Q chI chR γcI γcR $$ HcI HoI HcR HoR HprocEx
      with ⟨%inc, %res, %raws, %evs, %procd, %alive, #Hinc, #Hrc, Hps, Hproc, Hcons⟩
    (try wp_auto)
    wp_apply (wp_newBlockLogger _ _ _ _ _ _) $$ [] as %lgI #HlgI
    · iframe #
    (try wp_auto)
    iapply wp_fupd
    wp_apply (wp_newBlockLogger _ _ _ _ _ _) $$ [] as %lgR #HlgR
    · iframe #
    (try wp_auto)
    ipersist watcher
    ipersist key
    ipersist recursive
    ipersist progressNotify
    ipersist recordTimestamps
    ipersist internalPred
    ipersist ctx
    ipersist cancel
    ipersist incomingEventChan
    ipersist resultChan
    ipersist getResourceSizeEstimator
    ipersist incomingEventLogger
    ipersist resultLogger
    iapply HΦ
    iexists ⟨res, evs, inc, raws, gstop, gprodEx, gprocEx, γ'⟩, procd, alive, ctx'
    iframe
    imodintro
    isplitr [Hstop]
    · unfold kWcCons kWcProd
      isplitr
      · iexists wp, chI, chR, lgI, cf, rse, γ'
        iframe #
        have hPD : kCancelPD (GF := GF) (⟨res, evs, inc, raws, gstop, gprodEx, gprocEx, γ'⟩ : KWatchNames) cd =
            kCancelPD (⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx, gprocEx, ⟨gstop, gstop⟩⟩ : KWatchNames) cd := by
          unfold kCancelPD kStopped kProdExited kProcExited; rfl
        have hCdw : kCdw (GF := GF) (⟨res, evs, inc, raws, gstop, gprodEx, gprocEx, γ'⟩ : KWatchNames) cd =
            { cd with PDone := iprop(cd.PDone ∨ kCancelPD (⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx, gprocEx, ⟨gstop, gstop⟩⟩ : KWatchNames) cd), Done_gn := γ' } := by
          unfold kCdw; rw [hPD]
        rw [hCdw, hPD]
        isplitr
        · iexact Hcs
        isplitr
        · iexact Hctx'
        isplitr
        · iapply metadata.outgoingCtxOkC_from ci ctx' $$ [$Hvf $Hmd]
        isplitr
        · iapply clientWatchOk_ctxErr c.cl γk ctx' _ $$ [$Hcw $Hctx']
        ipureintro; exact ⟨rfl, Hklen, Hkp⟩
      · iexists pred, lgR
        iframe #
        ipureintro; exact Hpfx
    · unfold kLive
      iexact Hstop
  · ihave #Hsg : (k8s_io.apiserver.pkg.storage.etcd3.storageInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Psto
    icases Hsg with ⟨%rw, %tl, %pE, -, -, #HEv, #HEok⟩
    ihave #HselW := everything_selPredOkW wp_ShardingEnabled wp_labelFieldEmpty c.S pE sel
      (Hsp.2 rfl) $$ [$Psto $HEok]
    (try wp_auto)
    imod dghostVar_alloc (GF := GF) false with ⟨%gstop, Hstop⟩
    imod dghostVar_alloc (GF := GF) false with ⟨%gprodEx, HprodEx⟩
    imod dghostVar_alloc (GF := GF) false with ⟨%gprocEx, HprocEx⟩
    wp_apply (context.wp_WithCancel_ctx ci cd
      (kCancelPD (GF := GF) ⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx,
        gprocEx, ⟨gstop, gstop⟩⟩ cd)) $$ [] as %ctx' %γ' %cf ⟨#Hcs, #Hctx', -, #Hvf⟩
    · iframe #
    imod kWatch_alloc c W
      ⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx, gprocEx, γ'⟩
      cd sel true (kInScope kp recur) m Q chI chR γcI γcR $$ HcI HoI HcR HoR HprocEx
      with ⟨%inc, %res, %raws, %evs, %procd, %alive, #Hinc, #Hrc, Hps, Hproc, Hcons⟩
    (try wp_auto)
    wp_apply (wp_newBlockLogger _ _ _ _ _ _) $$ [] as %lgI #HlgI
    · iframe #
    (try wp_auto)
    iapply wp_fupd
    wp_apply (wp_newBlockLogger _ _ _ _ _ _) $$ [] as %lgR #HlgR
    · iframe #
    (try wp_auto)
    ipersist watcher
    ipersist key
    ipersist recursive
    ipersist progressNotify
    ipersist recordTimestamps
    ipersist internalPred
    ipersist ctx
    ipersist cancel
    ipersist incomingEventChan
    ipersist resultChan
    ipersist getResourceSizeEstimator
    ipersist incomingEventLogger
    ipersist resultLogger
    iapply HΦ
    iexists ⟨res, evs, inc, raws, gstop, gprodEx, gprocEx, γ'⟩, procd, alive, ctx'
    iframe
    imodintro
    isplitr [Hstop]
    · unfold kWcCons kWcProd
      isplitr
      · iexists wp, chI, chR, lgI, cf, rse, γ'
        iframe #
        have hPD : kCancelPD (GF := GF) (⟨res, evs, inc, raws, gstop, gprodEx, gprocEx, γ'⟩ : KWatchNames) cd =
            kCancelPD (⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx, gprocEx, ⟨gstop, gstop⟩⟩ : KWatchNames) cd := by
          unfold kCancelPD kStopped kProdExited kProcExited; rfl
        have hCdw : kCdw (GF := GF) (⟨res, evs, inc, raws, gstop, gprodEx, gprocEx, γ'⟩ : KWatchNames) cd =
            { cd with PDone := iprop(cd.PDone ∨ kCancelPD (⟨⟨γcR, gstop, gstop⟩, gstop, ⟨γcI, gstop, gstop⟩, gstop, gstop, gprodEx, gprocEx, ⟨gstop, gstop⟩⟩ : KWatchNames) cd), Done_gn := γ' } := by
          unfold kCdw; rw [hPD]
        rw [hCdw, hPD]
        isplitr
        · iexact Hcs
        isplitr
        · iexact Hctx'
        isplitr
        · iapply metadata.outgoingCtxOkC_from ci ctx' $$ [$Hvf $Hmd]
        isplitr
        · iapply clientWatchOk_ctxErr c.cl γk ctx' _ $$ [$Hcw $Hctx']
        ipureintro; exact ⟨rfl, Hklen, Hkp⟩
      · iexists pE, lgR
        iframe #
        ipureintro; exact Hpfx
    · unfold kLive
      iexact Hstop

end proof

end k8s
end EtcdGrove
end Perennial
