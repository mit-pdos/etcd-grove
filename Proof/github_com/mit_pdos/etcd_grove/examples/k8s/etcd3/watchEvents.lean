/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/watchEvents.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.consume
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Watch
public import Proof.context.LibKeysChain
public import Perennial.Proof.context.Results
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchEventsLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem watchEvents.wp_proof
    (wp_Watch : store.Watch.spec (GF := GF) (hG := hG))
    (wp_watchOptions : watchOptions.spec (GF := GF) (hG := hG))
    (wp_consume : consume.spec (GF := GF) (hG := hG))
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_Empty : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    watchEvents.spec (GF := GF) (hG := hG) := by
  intro _ _ _ sp c γk x k n Q hS hQ hQQ hnr htb hk hkl hn hn63
  wp_start as ⟨Hlt, #Hst, #Hsw, #Hwl, #Hrs, HQ0, #HQup⟩
  wp_auto
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init; iPkgInit
  wp_apply context.wp_Background
  imod dghostVar_alloc (GF := GF) false with ⟨%γd, Hdt⟩
  wp_apply context.wp_WithCancel_Background (donePD γd) $$ [$Pctx $Hcci]
    as %ctx %γc %cancel ⟨#Hcancel, #Hctx, -, #Hfrom⟩
  ihave #HoC := metadata.outgoingCtxOkC_bgFrom ctx $$ Hfrom
  ihave #Hk8 := k8sctx.k8sCtxOk_bgFrom ctx $$ [$Pctx $Hfrom]
  ihave #Hce := storeWatchOk_ctxErr sp c driverW γk ctx _ $$ [$Hsw $Hctx]
  wp_apply wp_watchOptions as %p Hp
  imod sendInitOwn_persist p (sieOfL x) $$ Hp with #Hsie
  ihave #Hsel := predOk_driverW wp_Matches wp_Empty wp_LM wp_LE wp_FM wp_FE wp_GA x x.Bookmarks' $$ Hpkg
  wp_apply (wp_Watch DObj sp c driverW γk ctx
      { Values := ∅, Deadline := none, Done_gn := γc, PDone := donePD γd } x.WKey' (watchOptsV x p)
      k n (sieOfL x) (selD x) (predEmptyL x) Q hQ hQQ hnr) $$ [$Hlt HQ0] as %wi %err ⟨Hlt, Hr⟩
  · iframe #
    iframe HQ0
    isplitr
    · ipureintro
      exact ⟨hk, hkl, hn, hn63, rfl, rfl⟩
    isplitr
    · rw [show (watchOptsV x p).SendInitialEvents' = p from rfl]; iexact Hsie
    isplitr
    · rw [hS, show (watchOptsV x p).Predicate' = predWV x x.Bookmarks' from rfl]; iexact Hsel
    ipureintro; exact htb
  icases Hr with (%Hf | ⟨%He, %γ, Hw⟩)
  · -- the `Watch` call failed: cancel, report it
    obtain ⟨hne, hs, hn0⟩ := Hf
    rcases err with eo | _
    rotate_left
    · exact absurd rfl hne
    imod dghostVar_update true γd false $$ Hdt with Hdt
    imod dghostVar_persist γd 1 true $$ Hdt with #Hdone
    wp_auto
    wp_apply Hcancel $$ [] as -
    · iunfold donePD; iexact Hdone
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    rw [ite_eq_left rfl]
    ipureintro; exact ⟨hs, hn0⟩
  subst He
  ihave Hdt : doneTok γd $$ [Hdt]
  · iunfold doneTok; iexact Hdt
  wp_auto
  wp_apply (wp_consume c wi γ _ γd (selD x) (predEmptyL x) (kScopeOf c k x.Recursive')
      (kModeOf (sieOfL x) x.Bookmarks' n) Q x hS rfl) $$ [$Hw $Hdt]
    as %sl %rsl ⟨%rs, %kes, Hsl, #Hrs, %Hrel, Hseen, #HSO, Hlive, Hdt⟩
  iunfold kStopOk at HSO
  icases HSO with ⟨%wo, %Hwo, #HStop⟩
  subst Hwo
  wp_auto
  wp_apply HStop $$ [Hlive] as -
  · ileft; iexact Hlive
  iunfold doneTok at Hdt
  imod dghostVar_update true γd false $$ Hdt with Hdt
  imod dghostVar_persist γd 1 true $$ Hdt with #Hdone
  wp_apply Hcancel $$ [] as -
  · iunfold donePD; iexact Hdone
  (try wp_auto)
  iapply HΦ
  iframe Hlt
  rw [ite_eq_right Bool.false_ne_true]
  iexists rs, kes
  iframe
  iframe #
  ipureintro; exact Hrel

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
