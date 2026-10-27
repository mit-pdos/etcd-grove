/-
Proof of `Spec/k8s_io/client_go/tools/cache/processorListener__run.lean`. Lean-first.

The loop's invariant: the notifications received are those of the events `evs` delivered so far
(`H evs`); `sleepAfterCrash` is `false` (every iteration resets it: no handler panics).
-/
module

public import Spec.k8s_io.client_go.tools.cache.processorListener__run
public import Spec.k8s_io.client_go.tools.cache.synctrack.SingleFileTracker__Finished
public import Spec.k8s_io.utils.trace.New
public import Spec.k8s_io.utils.trace.Trace__LogIfLong

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem processorListener.run.wp_proof
    (wp_Finished : synctrack.SingleFileTracker.Finished.spec (GF := GF) (hG := hG))
    (wp_tnew : EtcdGrove.trace.New.spec (GF := GF) (hG := hG))
    (wp_tlog : EtcdGrove.trace.Trace.LogIfLong.spec (GF := GF) (hG := hG)) :
    processorListener.run.spec (GF := GF) (hG := hG) := by
  intro l γ Q h H runFin
  wp_start as ⟨#Hl, #Hh', #Hhok, #Hrf, Hcons, HH, Hbc⟩
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache.synctrack $$ []
  · iPkgInit
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold isListener at Hl
  icases Hl with ⟨%addCh, %nextCh, %t, %h0, %lg, %hn, #Hadd, #Hnext, #Hlg, #Hhn, #Hh, #Ht,
    #Hsa, #Hsn, #Hsft, #Hlen⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iunfold lhOk at Hhok
  icases Hhok with ⟨%hi, %Hhi, #HOnAdd, #HOnUpdate, #HOnDelete⟩
  ihave HI : (∃ evs : List Ev,
      "Hcons" ∷ spscConsumer (V := GoInterface) γ.next (evs.map notifOf) ∗ "HH" ∷ H evs ∗
      "sleepAfterCrash" ∷ sleepAfterCrash_ptr ↦ false ∗
      "Hbc" ∷ ownBroadcastChan runFin γ.runFin iprop(True) .Pending ∗ "p" ∷ p_ptr ↦ l : IProp GF)
    $$ [Hcons HH sleepAfterCrash Hbc p]
  · iexists []; iframe
  wp_for HI
  wp_apply (wp_spsc_receive (t := go.InterfaceType []) γ.next nextCh _ _ (evs.map notifOf))
    $$ [$Hsn $Hcons] as %v %ok Hv
  cases ok
  · -- `nextCh` closed: the loop ends, `runFinished` closed (deferred)
    wp_auto
    wp_for_post
    wp_apply (wp_broadcast_chan_close runFin γ.runFin iprop(True)) $$ [$Hbc] as -
    · imodintro; itrivial
    iapply HΦ; itrivial
  simp only [↓reduceIte]
  icases Hv with ⟨HP, Hcons⟩
  iunfold notifP at HP
  icases HP with ⟨%e, %he, HQ, Htok⟩
  subst he
  wp_auto
  wp_apply wp_with_defer as %defer2 defer2
  (try wp_auto)
  wp_apply_core sync.atomic.Int64.wp_Load _ _ $$ [] [-]
  · iPkgInit
  iinv Hlen with ⟨%c, >Hc⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists c
  iframe Hc
  iintro Hc
  imod Hmask
  imod Hclose $$ [Hc] with -
  · inext; iexists _; iframe
  imodintro
  wp_auto
  -- the slow-handler trace, if many notifications are pending: either way, the deferred calls
  -- (`HandleCrashWithLogger`, and the trace's `LogIfLong`) return
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ p_ptr ↦ l ∗ ∃ df : GoFunc, defer2 ↦ df ∗
      □ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #df) (Val #())) {{ Ψ }}))))
    $$ [defer2 p pendingNotifications]
  · wp_if_destruct
    · (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fl ⟨Hfl, Hflc⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_tnew as %tr -
      (try wp_auto)
      iframe
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %Ψ HΨ
      wp_auto
      wp_apply wp_tlog
      (try wp_auto)
      wp_bind (App (Val #(functions k8s_io.apimachinery.pkg.util.runtime.HandleCrashWithLogger []))
        (Val #lg))
      iapply deferred_HandleCrashWithLogger
      inext
      wp_auto
      iexact HΨ
    · iframe
      imodintro
      iintro %Ψ HΨ
      wp_auto
      wp_bind (App (Val #(functions k8s_io.apimachinery.pkg.util.runtime.HandleCrashWithLogger []))
        (Val #lg))
      iapply deferred_HandleCrashWithLogger
      inext
      wp_auto
      iexact HΨ
  iintro %v ⟨%hv, p, %df, defer2, #Hdf⟩
  subst hv
  wp_auto
  icombine Hh Hh' gives %Heq
  subst Heq
  subst Hhi
  simp only [List.length_map, Int.toNat_natCast]
  -- the type switch: the notification's event, the handler's method on it
  cases e with
  | add o b =>
    simp only [notifOf, interface.mkOk]
    wp_auto
    ihave #H1 := HOnAdd $$ %evs %o %b
    wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
    iapply H1 $$ [$HH $HQ]
    inext
    iintro HH
    (try wp_auto)
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ p_ptr ↦ l))) $$ [Htok p]
    · cases b
      · wp_auto; iframe; ipureintro; rfl
      · simp only [Ev.initial, ↓reduceIte]
        wp_auto
        wp_apply wp_Finished $$ [$Hst $Hsft $Htok]
        (try wp_auto)
        iframe; ipureintro; rfl
    iintro %v ⟨%hv, p⟩
    subst hv
    wp_auto
    wp_apply Hdf
    (try wp_auto)
    wp_for_post
    iframe
    iexists evs ++ [Ev.add o b]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe
  | update a b =>
    simp only [notifOf, interface.mkOk]
    wp_auto
    ihave #H1 := HOnUpdate $$ %evs %a %b
    wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
    iapply H1 $$ [$HH $HQ]
    inext
    iintro HH
    (try wp_auto)
    wp_apply Hdf
    (try wp_auto)
    wp_for_post
    iframe
    iexists evs ++ [Ev.update a b]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe
  | delete o =>
    simp only [notifOf, interface.mkOk]
    wp_auto
    ihave #H1 := HOnDelete $$ %evs %o
    wp_bind (App (Val #(methods hi.ty go!"OnDelete" hi.v)) _)
    iapply H1 $$ [$HH $HQ]
    inext
    iintro HH
    (try wp_auto)
    wp_apply Hdf
    (try wp_auto)
    wp_for_post
    iframe
    iexists evs ++ [Ev.delete o]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe

end proof

end cache
end EtcdGrove
end Perennial
