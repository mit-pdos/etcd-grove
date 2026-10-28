/-
Proof of `Spec/k8s_io/client_go/tools/cache/processorListener__pop.lean`. Lean-first.

The loop's invariant: received on `addCh` = sent on `nextCh` ++ the pending notifications (the
`notification` variable, if not `nil`, then the ring), each pending one with its resource at its
position, one time receipt per pending notification (so the ring stays below `2^61`), and the
`nextCh` variable `nil` exactly when nothing is pending.
-/
module

public import Spec.k8s_io.client_go.tools.cache.processorListener__pop
public import Spec.k8s_io.utils.buffer.TypedRingGrowing__ReadOne
public import Spec.k8s_io.utils.buffer.TypedRingGrowing__WriteOne

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem processorListener.pop.wp_proof
    (wp_ReadOne : buffer.TypedRingGrowing.ReadOne.spec (GF := GF) (hG := hG))
    (wp_WriteOne : buffer.TypedRingGrowing.WriteOne.spec (GF := GF) (hG := hG)) :
    processorListener.pop.spec (GF := GF) (hG := hG) := by
  intro l γ Q done Hbound
  wp_start as ⟨#Hl, #Hdone', Hcons, Hprod, Hring, Hbc⟩
  ihave #Hbuf : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.buffer $$ []
  · iPkgInit
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold isListener at Hl
  icases Hl with ⟨%addCh, %nextCh, %t, %h, %lg, %hn, #Hadd, #Hnext, #Hlg, #Hhn, #Hh, #Ht,
    #Hsa, #Hsn, #Hsft, #Hlen⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  imod receipt_zero (GF := GF) with Hk0
  ihave HI : (∃ (nc : GoChan) (nv : GoInterface) (sn pend q : List GoInterface),
      "nextCh" ∷ nextCh_ptr ↦ nc ∗ "notification" ∷ notification_ptr ↦ nv ∗
      "Hcons" ∷ spscConsumer γ.add (sn ++ pend) ∗ "Hprod" ∷ spscProducer γ.next sn ∗
      "Hring" ∷ buffer.ownRing (structFieldRef processorListener go!"pendingNotifications" l) q ∗
      "%Hst" ∷ ⌜(nv = interface.nil ∧ nc = chan.nil ∧ pend = [] ∧ q = []) ∨
        (nv ≠ interface.nil ∧ nc = nextCh ∧ pend = nv :: q)⌝ ∗
      "HP" ∷ ([∗list] i ↦ v ∈ pend, notifP Q γ.tr ((sn.length : Int) + i) v) ∗
      "Hk" ∷ ⧗ q.length ∗
      "Hbc" ∷ ownBroadcastChan done γ.done iprop(True) .Pending ∗ "p" ∷ p_ptr ↦ l : IProp GF)
    $$ [nextCh notification Hcons Hprod Hring Hbc p Hk0]
  · iexists zero_val GoChan, GoInterface.nil, [], [], []
    simp only [named, List.append_nil, List.length_nil]
    iframe
    isplitr
    · ipureintro; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  wp_for_core
  iNamed HI
  wp_auto
  cleanup_bool_decide
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `case nextCh <- notification`: nothing pending (a nil channel), or the oldest pending one
    rcases Hst with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hnv, rfl, rfl⟩
    · iright
      iapply (chan.nilClausePre_send (V := GoInterface) _ _ _ rfl)
    ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, nc,
      γ.next.chanName, nv
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · unfold isSpsc; icases Hsn with ⟨$, -⟩
    icases (BigSepL.bigSepL_cons).1 $$ HP with ⟨HP0, HP⟩
    iapply spsc_send_au γ.next nc _ _ sn nv _ $$ Hsn [$Hlc1 $Hlc2 $Hlc3] [$Hprod HP0]
    · iframe
    inext
    iintro Hprod
    wp_auto
    wp_apply (wp_ReadOne _ q) $$ [$Hbuf $Hring] as %x %ok Hr
    cases q with
    | nil =>
      simp only
      icases Hr with ⟨%hr, Hring⟩
      obtain ⟨rfl, rfl⟩ := hr
      wp_auto
      wp_for_post
      iframe
      iexists chan.nil, GoInterface.nil, sn ++ [nv], [], []
      simp only [named, List.append_nil, List.length_nil]
      iframe
      isplitr
      · ipureintro; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
      · iapply BigSepL.bigSepL_nil.2; itrivial
    | cons y q' =>
      simp only
      icases Hr with ⟨%hr, Hring⟩
      obtain ⟨rfl, rfl⟩ := hr
      icases (receipt_add q'.length 1).1 $$ Hk with ⟨Hk, -⟩
      wp_auto
      wp_apply_core sync.atomic.Int64.wp_Add _ _ $$ [] [-]
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
      ihave %hy := notifP_nonnil Q γ.tr _ x $$ [HP]
      · icases (BigSepL.bigSepL_cons).1 $$ HP with ⟨HP0, -⟩; iexact HP0
      wp_for_post
      iframe
      iexists nc, x, sn ++ [nv], x :: q', q'
      simp only [named, List.append_assoc, List.singleton_append, List.length_append,
        List.length_singleton]
      iframe
      isplitr
      · ipureintro; right; refine ⟨hy, ?_, ?_⟩ <;> first | rfl | trivial
      iapply (BigSepL.bigSepL_mono (fun {i v} _ => by
        rw [show ((sn.length + 1 : Nat) : Int) + (i : Int) = (sn.length : Int) + ((i + 1 : Nat) : Int) by
          omega])) $$ HP
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `case notificationToAdd, ok := <-p.addCh`
    ileft
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, addCh,
      γ.add.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases Hsa with ⟨$, -⟩
    iapply spsc_rcv_au γ.add addCh _ _ (sn ++ pend) _ $$ Hsa [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · -- closed: return, the deferred calls run
      wp_auto
      wp_for_post
      wp_apply (wp_broadcast_chan_close done γ.done iprop(True)) $$ [$Hbc] as -
      · imodintro; itrivial
      wp_apply (wp_spsc_close (t := go.InterfaceType []) γ.next nextCh _ _ sn) $$ [$Hsn $Hprod]
      -- the deferred `utilruntime.HandleCrashWithLogger(p.logger)` (gap G-defer-variadic)
      wp_bind (App (Val #(functions k8s_io.apimachinery.pkg.util.runtime.HandleCrashWithLogger []))
        (Val #lg))
      iapply deferred_HandleCrashWithLogger
      inext
      wp_auto
      iapply HΦ; itrivial
    simp only [↓reduceIte]
    icases Hv with ⟨HPv, Hcons⟩
    ihave %hv := notifP_nonnil Q γ.tr _ v $$ [HPv]
    · iexact HPv
    wp_auto
    rcases Hst with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hnv, rfl, rfl⟩
    · -- nothing pending: `v` is
      wp_auto
      wp_for_post
      iframe
      iexists nextCh, v, sn, [v], []
      simp only [named, List.append_nil, List.length_nil]
      iframe
      isplitr
      · ipureintro; right; refine ⟨hv, ?_, ?_⟩ <;> first | rfl | trivial
      iapply BigSepL.bigSepL_cons.2
      iframe
      iapply BigSepL.bigSepL_nil.2; itrivial
    · -- some pending: `v` to the ring
      cases nv with
      | nil => exact absurd rfl hnv
      | ok i =>
      simp only
      wp_take_receipt as Hr
      icases receipt_add_one_lt q.length $$ [Hr Hk] with ⟨%Hlt, Hk⟩
      · iframe
      wp_apply (wp_WriteOne _ q v (by omega)) $$ [$Hbuf $Hring] as Hring
      wp_apply_core sync.atomic.Int64.wp_Add _ _ $$ [] [-]
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
      wp_for_post
      iframe
      iexists nc, GoInterface.ok i, sn, GoInterface.ok i :: (q ++ [v]), q ++ [v]
      simp only [named, List.length_append, List.length_singleton]
      iframe
      isplitl [Hcons]
      · rw [show sn ++ GoInterface.ok i :: (q ++ [v]) = (sn ++ GoInterface.ok i :: q) ++ [v] by simp]
        iexact Hcons
      isplitr
      · ipureintro; right; refine ⟨hnv, ?_, ?_⟩ <;> first | rfl | trivial
      rw [show GoInterface.ok i :: (q ++ [v]) = (GoInterface.ok i :: q) ++ [v] from rfl]
      iapply BigSepL.bigSepL_snoc.2
      iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end cache
end EtcdGrove
end Perennial
