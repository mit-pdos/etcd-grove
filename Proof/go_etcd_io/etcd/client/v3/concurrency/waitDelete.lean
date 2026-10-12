/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/waitDelete.lean`. Lean-first (no Rocq
counterpart).
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

/-- `Watch(key, WithRev(rev))` is a single-key watch from `rev` that does not panic. -/
theorem waitDelete_opts (key : GoString) (rev : w64) :
    (opWatchModel key [withRevM rev]).isRangeWatch rev = true ∧
      ¬ opWatchPanics key [withRevM rev] ∧ (opWatchModel key [withRevM rev]).key = key ∧
      (opWatchModel key [withRevM rev]).base.rangeEnd = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit, OpFull.newOp,
    OpModel.zero, withRevM, OpFull.isRangeWatch]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem waitDelete.wp_proof (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG)) :
    waitDelete.spec (GF := GF) (hG := hG) := by
  intro ctx cs client pfx key rev
  wp_start as ⟨#Hcl, #Hctx, #Hcc, %Hp⟩
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, -, #Hwf, -, -, -, -, -, #HW⟩
  wp_auto
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
  ihave IH : iprop(∃ (rcv : List go_etcd_io.etcd.client.v3.WatchResponse)
      (v : go_etcd_io.etcd.client.v3.WatchResponse),
      "Hcons" ∷ spscConsumer γw.spsc rcv ∗ "wr" ∷ wr_ptr ↦ v) $$ [Hcons wr]
  · iexists [], _
    simp only [named]
    iframe
  wp_for IH
  (try wp_auto)
  wp_bind (App (Val (chan.receive _)) _)
  wp_apply wp_spsc_receive γw.spsc wch
    (rangeWatchElem γw pfx (opWatchModel key [withRevM rev]) rev) (fun _ => iprop(True)) rcv
    $$ [$Hwch $Hcons] as %v' %ok H
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨-, %Hv⟩
    wp_auto
    wp_for_post
    wp_apply wp_Err wr_ptr v (DFrac.own 1) $$ [$wr] as %err ⟨wr, %Herr⟩
    cases err with
    | ok e =>
      wp_auto
      wp_apply Hcancel'
      · imodintro; itrivial
      (try wp_auto)
      iapply HΦ
      ileft; ipureintro; intro h; cases h
    | nil =>
      wp_auto
      ihave #Hctx2 := Hctx
      iNamed Hctx2
      ihave #HErrU := HErr $$ %Broadcast.Unknown
      wp_apply HErrU as %cerr -
      cases cerr with
      | ok e =>
        wp_auto
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        ileft; ipureintro; intro h; cases h
      | nil =>
        wp_auto
        wp_apply errors.wp_New as %e -
        (try wp_auto)
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        ileft; ipureintro; intro h; cases h
  simp only [↓reduceIte]
  icases H with ⟨HP, Hcons⟩
  iunfold rangeWatchElem at HP
  icases HP with ⟨%r, %c, %c', #Hevs, -, -, -, -, #Hok⟩
  iunfold eventsAt at Hevs
  icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
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
    · -- a delete event: `key` is absent at its revision
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
      iright
      isplitr
      · ipureintro; rfl
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
  iexists rcv ++ [v'], v'
  simp only [named]
  iframe

end proof

end concurrency
end EtcdGrove
end Perennial
