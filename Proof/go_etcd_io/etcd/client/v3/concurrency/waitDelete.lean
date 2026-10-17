/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/waitDelete.lean`. Lean-first (no Rocq
counterpart).

etcd#22387: the loop `select`s on three channels, its own watch of `key` (`wch`), `waitDeletes`'
watch of the waiter's key (`waitCh`, whose consumer it is given) and the context's `Done`. Each
receive is a clause of `chan.wp_select_blocking` (the clauses' preconditions are a conjunction:
only one fires, so both watch consumers are available to each). A delete event of `wch` returns
`nil` with `key` absent at its revision; one of `waitCh` returns `errWaitKeyDeleted` with `waitKey`
absent at its revision (`rangeWatchEvOk`); a closed channel returns the context's error or
`errLostWatcher`, an error response its error, and `Done` the context's (non-nil) error.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.waitDelete
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem waitDelete.wp_proof (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG)) :
    waitDelete.spec (GF := GF) (hG := hG) := by
  intro ctx cs client pfx key rev waitCh γ2 waitKey wrev rcv0
  wp_start as ⟨#Hcl, #Hctx, #Hcc, #Hwc, Hcons2, %Hp⟩
  ihave Hci : (concurrencyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, -, -, -, ⟨%eLW, #HeLW⟩, ⟨%eWK, #HeWK, -⟩⟩
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, -, #Hwf, -, -, -, -, -, #HW⟩
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  wp_apply context.wp_WithCancel iprop(True) ctx cs $$ [$Hctx $Hcc]
      as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx', #Hcc'⟩
  ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
  (try wp_auto)
  wp_apply wp_WithRev rev as %f #Hf
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  generalize hsl : slice.mk sl _ _ = optsSl
  ihave #Hopts : optsAt optsSl ([withRevM rev] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | i
    · cases Hf'; cases Hg; iexact Hf
    · simp at Hf'
  iunfold isEtcdRangeWatcher at HW
  ihave #HWa := HW $$ %ctx' %({ cs with PDone := iprop(cs.PDone ∨ True), Done_gn := γ' })
    %key %optsSl %([withRevM rev] : List (OpFull → OpFull)) %rev
  wp_auto
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := waitDelete_opts key rev
  wp_apply HWa $$ [] as %wch %γw ⟨#Hwch, Hcons, -⟩
  · iframe Hctx' Hopts
    ipureintro
    refine ⟨Hw1, Hw2, Hp.2, ?_⟩
    rw [Hw3, Hw4]; exact keyRangeUnder_key pfx key Hp.1
  obtain ⟨Hv1, Hv2, Hv3, Hv4⟩ := waitDelete_opts waitKey wrev
  ihave IH : iprop(∃ (rcv rcv2 : List go_etcd_io.etcd.client.v3.WatchResponse),
      "Hcons" ∷ spscConsumer γw.spsc rcv ∗ "Hcons2" ∷ spscConsumer γ2.spsc rcv2)
    $$ [Hcons Hcons2]
  · iexists [], rcv0
    simp only [named]
    iframe
  wp_for IH
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-wch`: the watch of `key`
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
      inferInstance, wch, γw.spsc.chanName
    isplit
    · ipureintro; rfl
    isplit
    · iunfold isSpsc at Hwch; icases Hwch with ⟨$, -⟩
    iapply spsc_rcv_au γw.spsc wch _ _ rcv $$ Hwch [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v' %ok H
    cases ok
    · -- closed: the context's error, or `errLostWatcher`
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨-, %Hv⟩
      wp_auto
      ihave #HErrU := HErr $$ %Broadcast.Unknown
      wp_apply HErrU as %cerr -
      cases cerr with
      | ok e =>
        wp_auto
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        iright; iright; ipureintro; intro h; cases h
      | nil =>
        wp_auto
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        iright; iright; ipureintro; intro h; cases h
    simp only [↓reduceIte]
    icases H with ⟨HP, Hcons⟩
    icases rangeWatchElem_closeErr $$ HP with ⟨#Hse, HP⟩
    iunfold rangeWatchElem at HP
    icases HP with ⟨%r, %c, %c', #Hevs, -, -, -, -, #Hok, -⟩
    iunfold eventsAt at Hevs
    icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
    wp_auto
    wp_apply wp_Err wr_ptr v' (DFrac.own 1) $$ [$wr $Hse] as %err ⟨wr, %Herr, -⟩
    cases err with
    | ok e =>
      wp_auto
      wp_for_post
      wp_apply Hcancel'
      · imodintro; itrivial
      (try wp_auto)
      iapply HΦ
      iright; iright; ipureintro; intro h; cases h
    | nil =>
    wp_auto
    ihave %Hsl := ownSlice_len $$ Hls
    ihave IH2 : iprop(∃ (n : w64) (e0 : Loc),
        "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝) $$ [i ev]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IH2
    wp_if_destruct
    · have Hlt : sint.nat n < ls.length := by word
      obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨e, He⟩ : ∃ e, r.events[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z v'.Events'.len := ⟨Hn.1, by word⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) l v'.Events' DFrac.discard ls Hn.1 Hl $$ Hls
        with ⟨#Hle, -⟩
      ihave #He := Hev $$ %(sint.nat n) %l %e %Hl %He
      iunfold eventAt at He
      icases He with ⟨%keySl, #Htyp, -⟩
      wp_auto
      wp_if_destruct
      · -- a delete event of `key`: absent at its revision
        iunfold rangeWatchRespOk at Hok
        icases Hok with ⟨-, #Hok⟩
        ihave #Hok' := Hok $$ %(sint.nat n) %e %He
        iunfold rangeWatchEvOk at Hok'
        icases Hok' with ⟨%Hke, #Hreach, #Habs, -⟩
        ihave #Habs' := Habs $$ %‹e.typ = W32 1›
        icases Habs' with ⟨#Habs', -⟩
        have Hek : e.key = key := by
          have := Hke.1; rw [Hw3, Hw4] at this; simpa [inRange] using this
        wp_for_post
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hcons2]
        · iexists _; iexact Hcons2
        iexists e.rev
        rw [← Hek]
        iframe Hreach Habs'
        ipureintro; exact Hke.2.1
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, l
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    (try wp_auto)
    wp_for_post
    iframe
    iexists rcv ++ [v'], rcv2
    simp only [named]
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-waitCh`: the watch of the waiter's key
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
      inferInstance, waitCh, γ2.spsc.chanName
    isplit
    · ipureintro; rfl
    iunfold waitKeyWatch at Hwc
    isplit
    · iunfold isSpsc at Hwc; icases Hwc with ⟨$, -⟩
    iapply spsc_rcv_au γ2.spsc waitCh _ _ rcv2 $$ Hwc [$Hlc1 $Hlc2] Hcons2
    inext
    iintro %v' %ok H
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨-, %Hv⟩
      wp_auto
      ihave #HErrU := HErr $$ %Broadcast.Unknown
      wp_apply HErrU as %cerr -
      cases cerr with
      | ok e =>
        wp_auto
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        iright; iright; ipureintro; intro h; cases h
      | nil =>
        wp_auto
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        iright; iright; ipureintro; intro h; cases h
    simp only [↓reduceIte]
    icases H with ⟨HP, Hcons2⟩
    icases rangeWatchElem_closeErr $$ HP with ⟨#Hse, HP⟩
    iunfold rangeWatchElem at HP
    icases HP with ⟨%r, %c, %c', #Hevs, -, -, -, -, #Hok, -⟩
    iunfold eventsAt at Hevs
    icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
    wp_auto
    wp_apply wp_Err wr_ptr v' (DFrac.own 1) $$ [$wr $Hse] as %err ⟨wr, %Herr, -⟩
    cases err with
    | ok e =>
      wp_auto
      wp_for_post
      wp_apply Hcancel'
      · imodintro; itrivial
      (try wp_auto)
      iapply HΦ
      iright; iright; ipureintro; intro h; cases h
    | nil =>
    wp_auto
    ihave %Hsl := ownSlice_len $$ Hls
    ihave IH2 : iprop(∃ (n : w64) (e0 : Loc),
        "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝) $$ [i ev]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IH2
    by_cases Hif : sint.Z n < sint.Z v'.Events'.len
    rotate_left
    · simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]
      wp_pures; cleanup_bool_decide; (try wp_auto)
      wp_for_post
      iframe
      iexists rcv, rcv2 ++ [v']
      simp only [named]
      iframe
    simp only [decide_eq_true Hif, ↓reduceIte]
    wp_pures; cleanup_bool_decide; (try wp_auto)
    · have Hlt : sint.nat n < ls.length := by word
      obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨e, He⟩ : ∃ e, r.events[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z v'.Events'.len := ⟨Hn.1, by word⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) l v'.Events' DFrac.discard ls Hn.1 Hl $$ Hls
        with ⟨#Hle, -⟩
      ihave #He := Hev $$ %(sint.nat n) %l %e %Hl %He
      iunfold eventAt at He
      icases He with ⟨%keySl, #Htyp, -⟩
      wp_auto
      wp_if_destruct
      · -- a delete event of `waitKey`: absent at its revision; `errWaitKeyDeleted`
        iunfold rangeWatchRespOk at Hok
        icases Hok with ⟨-, #Hok⟩
        ihave #Hok' := Hok $$ %(sint.nat n) %e %He
        iunfold rangeWatchEvOk at Hok'
        icases Hok' with ⟨%Hke, #Hreach, #Habs, -⟩
        ihave #Habs' := Habs $$ %‹e.typ = W32 1›
        icases Habs' with ⟨#Habs', -⟩
        have Hek : e.key = waitKey := by
          have := Hke.1; rw [Hv3, Hv4] at this; simpa [inRange] using this
        wp_for_post
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        iright; ileft
        isplitr
        · iunfold isPkgErr
          iframe HeWK
          ipureintro; intro h; cases h
        iexists e.rev
        rw [← Hek]
        iframe Hreach Habs'
        ipureintro; exact Hke.2.1
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, l
      simp only [named]
      iframe
      ipureintro; constructor <;> word
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-ctx.Done()`: the context's error, non-nil
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro ⟨-, #Hclosed⟩
    wp_auto
    ihave #HErrD := HErr $$ %Broadcast.Done
    wp_apply HErrD $$ Hclosed as %cerr %Hcne
    wp_for_post
    wp_apply Hcancel'
    · imodintro; itrivial
    (try wp_auto)
    iapply HΦ
    iright; iright; ipureintro; exact Hcne
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end concurrency
end EtcdGrove
end Perennial
