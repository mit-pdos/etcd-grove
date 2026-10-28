/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__whileProcessing_locked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__whileProcessing_locked
public import Spec.time.Duration__Seconds

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `int64` is not an interface type (instance search does not unfold `go.int64`): what
`MethodResolve` needs of `time.Duration` for `d.Seconds()`. -/
instance notInterface_int64_fifo : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩

theorem RealFIFO.whileProcessing_locked.wp_proof
    (wp_sec : time.Duration.Seconds.spec (GF := GF) (hG := hG)) :
    RealFIFO.whileProcessing_locked.spec (GF := GF) (hG := hG) := by
  intro f γ OK ch uwp mp h pf R
  wp_start as ⟨#Hguard, #Hinv, #Huwp, #Hbs, #Hmp, #Hh, #Hhok, Hlk, HR, Hwp⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iunfold fifoRes at HR
  icases HR with ⟨%q, %sl, %vs, Hex, Hst, Hsy, Hitems, Hsl, Hcap, Hds, Hpop, Hinit, %Hic,
    Hsc, Hcl, Hbc⟩
  cases h with
  | nil => iunfold obsOk at Hhok; icases Hhok with ⟨⟩
  | ok hi =>
  iunfold obsOk at Hhok
  cases uwp with
  | false =>
    (try wp_auto)
    wp_apply time.wp_Now as %t0 -
    (try wp_auto)
    wp_apply_core wp_wand $$ Hwp
    iintro %r ⟨%err, %hr, HRe⟩
    subst hr
    (try wp_auto)
    wp_apply time.wp_Since as %el -
    (try wp_auto)
    wp_apply wp_sec as %x -
    (try wp_auto)
    wp_apply Hhok
    (try wp_auto)
    iapply HΦ
    iframe
    iunfold fifoRes
    iexists q, sl, vs
    iframe
    ipureintro; exact Hic
  | true =>
    wp_auto_lc 1
    wp_if_destruct
    · imod fifo_release f γ OK ch $$ Hinv Hlc1 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
        with Htok
      · iunfold fifoRes
        iexists q, sl, vs
        iframe
        ipureintro; exact Hic
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
      (try wp_auto)
      wp_apply time.wp_Now as %t0 -
      (try wp_auto)
      wp_apply_core wp_wand $$ Hwp
      iintro %r ⟨%err, %hr, HRe⟩
      subst hr
      (try wp_auto)
      wp_apply time.wp_Since as %el -
      (try wp_auto)
      wp_apply wp_sec as %x -
      (try wp_auto)
      wp_apply Hhok
      (try wp_auto)
      iapply wp_fupd
      wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, Htok⟩
      imod fifo_acquire f γ OK ch $$ Hinv Hlc1 Hlc2 Htok with HR
      imodintro
      wp_auto
      iapply HΦ
      iframe
    · (try wp_auto)
      wp_apply time.wp_Now as %t0 -
      (try wp_auto)
      wp_apply_core wp_wand $$ Hwp
      iintro %r ⟨%err, %hr, HRe⟩
      subst hr
      (try wp_auto)
      wp_apply time.wp_Since as %el -
      (try wp_auto)
      wp_apply wp_sec as %x -
      (try wp_auto)
      wp_apply Hhok
      (try wp_auto)
      iapply HΦ
      iframe
      iunfold fifoRes
      iexists q, sl, vs
      iframe
      ipureintro; exact Hic


end proof

end cache
end EtcdGrove
end Perennial
