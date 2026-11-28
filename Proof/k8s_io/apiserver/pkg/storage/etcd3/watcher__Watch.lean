/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watcher__Watch.lean` (k8s 7f-5b). The start revision's
read (`GetCurrentResourceVersion`, through the watcher's `getCurrentStorageRV`) fires the caller's
`Q 0` (`readAus_crv`), which gives `kStartPre` without initial events at revision 0; the mode's flags
are `run`'s arguments; the result's methods are `ResultChan` and `Stop` (`kWcProd`'s fields).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watcher__Watch
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watcher__createWatchChan
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watcher__getStartWatchResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GetCurrentResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__run
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__Stop
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__ResultChan
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.isInitialEventsEndBookmarkRequired
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.areInitialEventsRequired
public import Spec.k8s_io.apiserver.pkg.util.flowcontrol.WatchInitialized
public import Spec.strings.HasSuffix
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
theorem watcher.Watch.wp_proof
    (wp_HasSuffix : strings.HasSuffix.spec (GF := GF) (hG := hG))
    (wp_getStart : watcher.getStartWatchResourceVersion.spec (GF := GF) (hG := hG))
    (wp_GetCRV : store.GetCurrentResourceVersion.spec (GF := GF) (hG := hG))
    (wp_createWatchChan : watcher.createWatchChan.spec (GF := GF) (hG := hG))
    (wp_isInitial : isInitialEventsEndBookmarkRequired.spec (GF := GF) (hG := hG))
    (wp_areInitial : areInitialEventsRequired.spec (GF := GF) (hG := hG))
    (wp_run : watchChan.run.spec (GF := GF) (hG := hG))
    (wp_WatchInitialized : flowcontrol.WatchInitialized.spec (GF := GF) (hG := hG))
    (wp_Stop : watchChan.Stop.spec (GF := GF) (hG := hG))
    (wp_ResultChan : watchChan.ResultChan.spec (GF := GF) (hG := hG)) :
    watcher.Watch.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ _ wp sp c W γk ci cd kp n opts sie sel emp Q HQok Hhist Hnr Hpfx Hkp Hklen Hsuf Hn
    Hpn Hrt
  wp_start as ⟨Hlt, #Hst, #Hsw, #Hwp, #Hsie, #Hsel, #Hwl, #Hrs, #Hctx, #Hmd, #Hce, #Hsig, %Htb, #Hra,
    #Hre⟩
  ihave #Hsw' := Hsw
  iunfold storeWatchOk at Hsw'
  icases Hsw' with ⟨%wp', %nf, %crv, %rse, #Hsw2, -, -, -, -, -, -, #Hwcrv, -, -, #Hcrv, -, -, -, -⟩
  ihave %Hwp := typedPointsto_agree_wand _ _ _ _ _ $$ Hwp Hsw2
  subst Hwp
  ihave #Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hlst⟩
  iunfold storeListOk at Hlst
  icases Hlst with ⟨%lf, %lγ, -, -, -, -, %Hrp⟩
  have hrpl : (c.pathPrefix ++ c.resourcePrefix).length ≤ opKeyMax :=
    Nat.le_trans (List.IsPrefix.length_le Hpfx) Hklen
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  cases hr : opts.Recursive'
  case true =>
    wp_auto
    wp_apply (wp_HasSuffix kp go!"/") $$ [$Pstr]
    rw [decide_eq_true (Hsuf hr)]
    wp_auto
    rw [Hpn]
    wp_auto
    wp_apply (wp_getStart wp crv (GoInterface.ok ci) n opts sie
      (fun r err => iprop(⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗
        ∃ σ : KVState, □ Q 0 σ ∗ ⌜r = W64 (σ.rev : Int)⌝)))) $$ [$Hlt] as %r0 %err ⟨Hlt, Hr0⟩
    · iframe #
      iintro %_ Hlt
      iapply Hcrv
      wp_apply (wp_GetCRV Obj sp c ci cd c.resourcePrefix (fun _ _ => Q 0) Hrp hrpl) $$ [$Hlt]
        as %m %e ⟨Hlt, Hout⟩
      · iframe #
        isplitr
        · iapply ctxOk_of_isContext $$ [$Hctx $Hmd]
        iapply readAus_crv $$ Hra
      iexists m, e
      isplitr
      · ipureintro; rfl
      iframe Hlt
      iexists m, e
      isplitr
      · ipureintro; rfl
      icases Hout with (⟨%He, -⟩ | ⟨%He, %σ1, #HQ1, %Hσ1⟩)
      · ileft; ipureintro; exact He
      · iright
        isplitr
        · ipureintro; exact He
        iexists σ1
        iframe #
        ipureintro; exact Hσ1.1
    ihave Hs : (⌜err ≠ GoInterface.nil ∧ sie = some false ∧ uint.nat n = 0⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ kStartPre (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q r0))
        $$ [Hr0]
    · unfold kStartPre kModeOf
      simp only
      by_cases hpos : 0 < sint.Z n
      · rw [if_pos hpos]
        icases Hr0 with %Hr0
        obtain ⟨rfl, rfl⟩ := Hr0
        iright
        isplitr
        · ipureintro; rfl
        split
        · ipureintro; constructor <;> word
        · split
          · ipureintro; constructor <;> word
          · exfalso; rename_i h1 h2; apply h2; word
      · rw [if_neg hpos]
        have hn0 : uint.nat n = 0 := by word
        by_cases hsf : sie = some false
        · rw [if_pos hsf]
          icases Hr0 with ⟨%m', Hm, %Hr0⟩
          icases Hm with (%He | ⟨%He, %σ1, #HQ1, %Hm'⟩)
          · ileft; ipureintro; exact ⟨He, hsf, hn0⟩
          · iright
            isplitr
            · ipureintro; exact He
            rw [if_pos He] at Hr0
            subst Hr0 Hm'
            have hfi : ¬ ((sie = none ∧ uint.nat n = 0) ∨ sie = some true) := by
              rintro (⟨h, -⟩ | h) <;> simp_all
            rw [if_neg (by simpa using hfi), if_neg (by omega)]
            iexists 0, σ1
            iframe #
            ihave %Hq := HQok 0 σ1 $$ HQ1
            ipureintro; exact ⟨rfl, Hq.2.2.2.2.2⟩
        · rw [if_neg hsf]
          icases Hr0 with %Hr0
          obtain ⟨rfl, rfl⟩ := Hr0
          iright
          isplitr
          · ipureintro; rfl
          have hfi : (sie = none ∧ uint.nat n = 0) ∨ sie = some true := by
            cases sie with
            | none => exact Or.inl ⟨rfl, hn0⟩
            | some b => cases b <;> simp_all
          rw [if_pos (by simpa using hfi)]
          ipureintro; constructor <;> word
    icases Hs with (%He | ⟨%He, Hsp⟩)
    · have hne := He.1
      cases err with
      | nil => exact absurd rfl hne
      | ok ei =>
        wp_auto
        iapply HΦ
        iframe Hlt
        ileft; ipureintro; exact He
    subst He
    wp_auto
    rw [Hpn, Hrt, hr]
    wp_apply (wp_createWatchChan Obj wp sp c W γk ci cd kp r0 _ opts.Predicate' sel emp
      (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q Hpfx Hkp Hklen) $$ []
      as %wc ⟨%γ, %procd, %alive, %ctx', #Hcons, Hir, Hps, Hpe, Hproc, Hcons2, Hlive⟩
    · iframe #
    (try wp_auto)
    wp_apply (wp_isInitial opts sie) $$ []
    · iframe #
    (try wp_auto)
    wp_apply (wp_areInitial n opts sie) $$ []
    · iframe #
    (try wp_auto)
    have Hbm : (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).bmReq = true →
        (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).forceInit = true := by
      intro h
      simp only [kModeOf, decide_eq_true_eq] at h ⊢
      exact Or.inr h.1
    wp_apply wp_fork_tok
    iintro Htok
    isplitl [Hir Hsp Hps Hpe Hproc Htok]
    · rw [show decide (sie = some true ∧ opts.Predicate'.AllowWatchBookmarks' = true) =
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).bmReq from rfl,
        show decide ((sie = none ∧ uint.nat n = 0) ∨ sie = some true) =
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).forceInit from rfl]
      wp_apply (wp_run Obj wc sp c W γk γ cd sel emp _
        (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q procd alive ctx' kp _ r0
        HQok Hhist Hnr Hbm hrpl) $$ [Hir Hsp Hps Hpe Hproc Htok] as Htok
      · iframe #
        iframe
        ipureintro; exact Htb
      iframe Htok
      ipureintro; exact isPanic_intoVal ()
    (try wp_auto)
    ihave #Pfc : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.flowcontrol $$ []
    · iPkgInit
    wp_apply (wp_WatchInitialized ci) $$ [$Pfc $Hsig]
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitr
    · ipureintro; rfl
    iexists γ
    iunfold kWcCons at Hcons
    icases Hcons with ⟨#Hprod, -⟩
    iunfold kWcProd at Hprod
    icases Hprod with ⟨%wp2, %chI, %chR, %lgI, %cf, %rse2, %γc, -, -, -, -, -, -, -, #Hfcf, #Hcs, -, -,
      -, -, -, -, #HfR, #Hrc, -, -, -, -⟩
    unfold k8sWatch
    iexists ⟨_, #wc⟩, chR
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %Φ' HΦ'
      iapply (wp_ResultChan wc chR) $$ [$HfR]
      inext
      iintro -
      iexact HΦ'
    isplitr
    · imodintro
      iintro %Φ' Hl HΦ'
      iapply (wp_Stop wc cf γc γ cd) $$ [$Hfcf $Hcs $Hl]
      iexact HΦ'
    iframe
    iapply kResChan_isSpsc $$ Hrc
  case false =>
    wp_auto
    rw [Hpn]
    wp_auto
    wp_apply (wp_getStart wp crv (GoInterface.ok ci) n opts sie
      (fun r err => iprop(⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗
        ∃ σ : KVState, □ Q 0 σ ∗ ⌜r = W64 (σ.rev : Int)⌝)))) $$ [$Hlt] as %r0 %err ⟨Hlt, Hr0⟩
    · iframe #
      iintro %_ Hlt
      iapply Hcrv
      wp_apply (wp_GetCRV Obj sp c ci cd c.resourcePrefix (fun _ _ => Q 0) Hrp hrpl) $$ [$Hlt]
        as %m %e ⟨Hlt, Hout⟩
      · iframe #
        isplitr
        · iapply ctxOk_of_isContext $$ [$Hctx $Hmd]
        iapply readAus_crv $$ Hra
      iexists m, e
      isplitr
      · ipureintro; rfl
      iframe Hlt
      iexists m, e
      isplitr
      · ipureintro; rfl
      icases Hout with (⟨%He, -⟩ | ⟨%He, %σ1, #HQ1, %Hσ1⟩)
      · ileft; ipureintro; exact He
      · iright
        isplitr
        · ipureintro; exact He
        iexists σ1
        iframe #
        ipureintro; exact Hσ1.1
    ihave Hs : (⌜err ≠ GoInterface.nil ∧ sie = some false ∧ uint.nat n = 0⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ kStartPre (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q r0))
        $$ [Hr0]
    · unfold kStartPre kModeOf
      simp only
      by_cases hpos : 0 < sint.Z n
      · rw [if_pos hpos]
        icases Hr0 with %Hr0
        obtain ⟨rfl, rfl⟩ := Hr0
        iright
        isplitr
        · ipureintro; rfl
        split
        · ipureintro; constructor <;> word
        · split
          · ipureintro; constructor <;> word
          · exfalso; rename_i h1 h2; apply h2; word
      · rw [if_neg hpos]
        have hn0 : uint.nat n = 0 := by word
        by_cases hsf : sie = some false
        · rw [if_pos hsf]
          icases Hr0 with ⟨%m', Hm, %Hr0⟩
          icases Hm with (%He | ⟨%He, %σ1, #HQ1, %Hm'⟩)
          · ileft; ipureintro; exact ⟨He, hsf, hn0⟩
          · iright
            isplitr
            · ipureintro; exact He
            rw [if_pos He] at Hr0
            subst Hr0 Hm'
            have hfi : ¬ ((sie = none ∧ uint.nat n = 0) ∨ sie = some true) := by
              rintro (⟨h, -⟩ | h) <;> simp_all
            rw [if_neg (by simpa using hfi), if_neg (by omega)]
            iexists 0, σ1
            iframe #
            ihave %Hq := HQok 0 σ1 $$ HQ1
            ipureintro; exact ⟨rfl, Hq.2.2.2.2.2⟩
        · rw [if_neg hsf]
          icases Hr0 with %Hr0
          obtain ⟨rfl, rfl⟩ := Hr0
          iright
          isplitr
          · ipureintro; rfl
          have hfi : (sie = none ∧ uint.nat n = 0) ∨ sie = some true := by
            cases sie with
            | none => exact Or.inl ⟨rfl, hn0⟩
            | some b => cases b <;> simp_all
          rw [if_pos (by simpa using hfi)]
          ipureintro; constructor <;> word
    icases Hs with (%He | ⟨%He, Hsp⟩)
    · have hne := He.1
      cases err with
      | nil => exact absurd rfl hne
      | ok ei =>
        wp_auto
        iapply HΦ
        iframe Hlt
        ileft; ipureintro; exact He
    subst He
    wp_auto
    rw [Hpn, Hrt, hr]
    wp_apply (wp_createWatchChan Obj wp sp c W γk ci cd kp r0 _ opts.Predicate' sel emp
      (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q Hpfx Hkp Hklen) $$ []
      as %wc ⟨%γ, %procd, %alive, %ctx', #Hcons, Hir, Hps, Hpe, Hproc, Hcons2, Hlive⟩
    · iframe #
    (try wp_auto)
    wp_apply (wp_isInitial opts sie) $$ []
    · iframe #
    (try wp_auto)
    wp_apply (wp_areInitial n opts sie) $$ []
    · iframe #
    (try wp_auto)
    have Hbm : (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).bmReq = true →
        (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).forceInit = true := by
      intro h
      simp only [kModeOf, decide_eq_true_eq] at h ⊢
      exact Or.inr h.1
    wp_apply wp_fork_tok
    iintro Htok
    isplitl [Hir Hsp Hps Hpe Hproc Htok]
    · rw [show decide (sie = some true ∧ opts.Predicate'.AllowWatchBookmarks' = true) =
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).bmReq from rfl,
        show decide ((sie = none ∧ uint.nat n = 0) ∨ sie = some true) =
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n).forceInit from rfl]
      wp_apply (wp_run Obj wc sp c W γk γ cd sel emp _
        (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q procd alive ctx' kp _ r0
        HQok Hhist Hnr Hbm hrpl) $$ [Hir Hsp Hps Hpe Hproc Htok] as Htok
      · iframe #
        iframe
        ipureintro; exact Htb
      iframe Htok
      ipureintro; exact isPanic_intoVal ()
    (try wp_auto)
    ihave #Pfc : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.flowcontrol $$ []
    · iPkgInit
    wp_apply (wp_WatchInitialized ci) $$ [$Pfc $Hsig]
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitr
    · ipureintro; rfl
    iexists γ
    iunfold kWcCons at Hcons
    icases Hcons with ⟨#Hprod, -⟩
    iunfold kWcProd at Hprod
    icases Hprod with ⟨%wp2, %chI, %chR, %lgI, %cf, %rse2, %γc, -, -, -, -, -, -, -, #Hfcf, #Hcs, -, -,
      -, -, -, -, #HfR, #Hrc, -, -, -, -⟩
    unfold k8sWatch
    iexists ⟨_, #wc⟩, chR
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %Φ' HΦ'
      iapply (wp_ResultChan wc chR) $$ [$HfR]
      inext
      iintro -
      iexact HΦ'
    isplitr
    · imodintro
      iintro %Φ' Hl HΦ'
      iapply (wp_Stop wc cf γc γ cd) $$ [$Hfcf $Hcs $Hl]
      iexact HΦ'
    iframe
    iapply kResChan_isSpsc $$ Hrc

end proof

end k8s
end EtcdGrove
end Perennial
