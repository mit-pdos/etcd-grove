/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__waitRescind.lean`. Lean-first (no
Rocq counterpart). Modelled on `concurrency/waitDelete.lean`: `nil` after a delete event (the lease
key absent at its revision), and also `nil` when the watch channel closes while `ctx` is not done
(the third disjunct of the spec, the finding).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitRescind
public import Spec.go_etcd_io.etcd.client.v3.WithRev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-- `Watch(key, WithRev(rev))` is a single-key watch from `rev` that does not panic. -/
theorem waitRescind_opts (key : GoString) (rev : w64) :
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
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.waitRescind.wp_proof (wp_WithRev : WithRev.spec (GF := GF) (hG := hG)) :
    leasingKV.waitRescind.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key rev
  wp_start as ⟨#Hlkv, #Hctx, #Hcc, %Hrev⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hclf, #Hkvf, #Hpfxf, #Hctxf,
    #Hcancelf, #Hoslf, -, -, -, #HLC, -⟩
  iunfold isLeasingClient at HLC
  icases HLC with ⟨-, ⟨%w, #HWf, #HW⟩, -⟩
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  wp_apply context.wp_WithCancel iprop(True) ctx cs $$ [$Hctx $Hcc]
      as %ctx' %γ' %cancel' ⟨#Hcancel, #Hctx', #Hcc'⟩
  ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
  (try wp_auto)
  wp_apply wp_WithRev (rev + W64 1) as %f #Hf
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  generalize hsl : slice.mk sl _ _ = optsSl
  ihave #Hopts : optsAt optsSl ([withRevM (rev + W64 1)] : List (OpFull → OpFull)) $$ []
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
    %(pfx ++ key) %optsSl %([withRevM (rev + W64 1)] : List (OpFull → OpFull)) %(rev + W64 1)
  wp_auto
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := waitRescind_opts (pfx ++ key) (rev + W64 1)
  wp_apply HWa $$ [] as %wch %γw ⟨#Hwch, Hcons, -⟩
  · iframe Hctx' Hopts
    ipureintro
    refine ⟨Hw1, Hw2, by word, ?_⟩
    rw [Hw3, Hw4]; intro k _; exact List.nil_prefix
  ihave IH : iprop(∃ (rcv : List go_etcd_io.etcd.client.v3.WatchResponse)
      (v : go_etcd_io.etcd.client.v3.WatchResponse),
      "Hcons" ∷ spscConsumer γw.spsc rcv ∗ "resp" ∷ resp_ptr ↦ v) $$ [Hcons resp]
  · iexists [], _
    simp only [named]
    iframe
  wp_for IH
  (try wp_auto)
  wp_bind (App (Val (chan.receive _)) _)
  wp_apply wp_spsc_receive γw.spsc wch
    (rangeWatchElem γw [] (opWatchModel (pfx ++ key) [withRevM (rev + W64 1)]) (rev + W64 1))
    (fun _ => iprop(True)) rcv
    $$ [$Hwch $Hcons] as %v' %ok H
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  cases ok
  · -- the channel closed without a delete event
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨-, %Hv⟩
    wp_auto
    wp_for_post
    wp_apply HErrU as %cerr -
    wp_apply Hcancel'
    · imodintro; itrivial
    (try wp_auto)
    iapply HΦ
    cases cerr with
    | ok e => ileft; ipureintro; intro h; cases h
    | nil => iright; iright; ipureintro; rfl
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
    · -- a delete event: the lease key is absent at its revision
      iunfold rangeWatchRespOk at Hok
      icases Hok with ⟨-, #Hok⟩
      ihave #Hok' := Hok $$ %(sint.nat n) %e %He
      iunfold rangeWatchEvOk at Hok'
      icases Hok' with ⟨%Hke, #Hreach, #Habs, -⟩
      ihave #Habs' := Habs $$ %‹e.typ = W32 1›
      icases Habs' with ⟨#Habs', -⟩
      have Hek : e.key = pfx ++ key := by
        have := Hke.1; rw [Hw3, Hw4] at this; simpa [inRange] using this
      wp_apply HErrU as %cerr -
      wp_for_post
      wp_for_post
      wp_apply Hcancel'
      · imodintro; itrivial
      (try wp_auto)
      iapply HΦ
      cases cerr with
      | ok e' => ileft; ipureintro; intro h; cases h
      | nil =>
        iright; ileft
        isplitr
        · ipureintro; rfl
        unfold leaseKeyDeleted
        iexists e.rev
        rw [← Hek]
        iframe Hreach Habs'
        ipureintro
        have := Hke.2.1
        have h1 : sint.Z (rev + W64 1) = sint.Z rev + 1 := by word
        omega
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

end leasing
end EtcdGrove
end Perennial
