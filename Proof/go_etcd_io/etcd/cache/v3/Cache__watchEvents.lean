/-
Proof of `Spec/Cache__watchEvents.lean`. Lean-first (no Rocq counterpart).

The loop's invariant: the client watch's consumer at cursor `k` (at or above `rev - 1`), the
demux's writer at state `cc`, the `applyErr` consumer, and the `Once`'s state: armed (the
caller's half of `γo` is `false`, the cursor still `rev - 1`) or run (`□ true`, the stream
continues the watch at `k` and at `rev - 1`: `CursorOk`). `readyOnce.Do` is
`Once.wp_Do_frame`, lending the writer (and, when armed, the caller's half) to the closure.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__watchEvents
public import Spec.go_etcd_io.etcd.cache.v3.demux__Init
public import Spec.go_etcd_io.etcd.cache.v3.demux__Broadcast
public import Spec.go_etcd_io.etcd.cache.v3.ready__Set
public import Spec.go_etcd_io.etcd.cache.v3.ready__Reset
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithProgressNotify
public import Spec.go_etcd_io.etcd.client.v3.WithCreatedNotify
public import Proof.go_etcd_io.etcd.cache.v3.OnceFrame

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

/-! ## Pure lemmas -/

/-- The options of `watchEvents`'s watch make a prefix watch from `rev` that does not panic. -/
theorem watchEvents_opts (pfx : GoString) (rev : w64) :
    (opWatchModel pfx [withPrefixM, withRevM rev, withProgressNotifyM, withCreatedNotifyM]).isPrefixWatch
        pfx rev = true ∧
      ¬ opWatchPanics pfx [withPrefixM, withRevM rev, withProgressNotifyM, withCreatedNotifyM] := by
  by_cases h : pfx = []
  · subst h
    simp [opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit, OpFull.newOp,
      OpModel.zero, withPrefixM, withRevM, withProgressNotifyM, withCreatedNotifyM,
      OpFull.isPrefixWatch]
  · simp [opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit, OpFull.newOp,
      OpModel.zero, withPrefixM, withRevM, withProgressNotifyM, withCreatedNotifyM,
      OpFull.isPrefixWatch, h]

/-- A progress step from the cursor extends `TailOk`. -/
theorem tailOk_step {pfx : GoString} {last : Int} {k p : w64} (h : TailOk pfx last k)
    (hs : EtcdStep k p pfx []) : TailOk pfx last p := by
  rcases h with h | ⟨q, hq, hs'⟩
  · exact Or.inr ⟨k, h, hs⟩
  · exact Or.inr ⟨q, hq, etcdStep_compose q k p pfx [] hs' hs⟩

/-- After `Init(rev)` the stream continues a watch at `rev - 1`, and the writer's invariant
holds. -/
theorem initCore_ok (pfx : GoString) (cap : Nat) (c : DemuxCore) (rev : w64)
    (hinv : DemuxInv cap c) (hw : WriterOk pfx c) (hrev : 0 < sint.Z rev) :
    CursorOk pfx (initCore c rev).1 (rev - W64 1) ∧ WriterOk pfx (initCore c rev).1 := by
  have hr1 : sint.Z (rev - W64 1) = sint.Z rev - 1 := by word
  have hne : rev ≠ W64 0 := by intro h; subst h; simp at hrev
  unfold initCore
  rw [ite_eq_right hne]
  by_cases h0 : c.minRev = W64 0
  · rw [ite_eq_left h0]
    obtain ⟨hs, hm⟩ := hinv.uninit h0
    refine ⟨⟨hne, ?_, Or.inl ?_⟩, fun h => absurd hm h⟩
    · show sint.Z rev - 1 ≤ sint.Z (rev - W64 1); omega
    · unfold DemuxCore.lastRev; rw [hs]; show sint.Z (rev - W64 1) ≤ sint.Z rev - 1; omega
  rw [ite_eq_right h0]
  have hinit : CursorOk pfx { DemuxCore.init with minRev := rev, base := sint.Z rev - 1 }
      (rev - W64 1) ∧ WriterOk pfx { DemuxCore.init with minRev := rev, base := sint.Z rev - 1 } := by
    refine ⟨⟨hne, ?_, Or.inl ?_⟩, fun h => absurd rfl h⟩
    · show sint.Z rev - 1 ≤ sint.Z (rev - W64 1); omega
    · show sint.Z (rev - W64 1) ≤ sint.Z rev - 1; omega
  by_cases h2 : c.maxRev = W64 0
  · rw [ite_eq_left h2]; exact hinit
  rw [ite_eq_right h2]
  by_cases h3 : rev = c.maxRev + W64 1
  · rw [ite_eq_left h3]
    have hk : rev - W64 1 = c.maxRev := by rw [h3]; bv_omega
    rw [hk]
    exact ⟨⟨h0, hinv.base_maxRev h2, hw h2⟩, hw⟩
  · rw [ite_eq_right h3]; exact hinit

/-- The pure part of etcd's watch contract for a response that is not an error: the created
notification, a progress notification, or events. -/
def WatchCase (pfx : GoString) (k k' : w64) (r : RespModel) : Prop :=
  sint.Z r.hdrRev < 2 ^ 63 - 1 ∧
  ((r.created = true ∧ r.events = [] ∧ k' = k) ∨
   (r.isProgressNotify = true ∧ sint.Z k ≤ sint.Z r.hdrRev ∧ k' = r.hdrRev ∧
     EtcdStep k r.hdrRev pfx []) ∨
   (r.events ≠ [] ∧ EvRevSorted r.events ∧
     (∀ e ∈ r.events, sint.Z k < sint.Z e.rev ∧ sint.Z e.rev < 2 ^ 63 - 1) ∧
     r.events.getLast?.map EvModel.rev = some k'))

theorem isProgressNotify_events {r : RespModel} (h : r.isProgressNotify = true) :
    r.events = [] := by
  unfold RespModel.isProgressNotify at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.1.1.1.1

theorem isProgressNotify_false_of_events {r : RespModel} (h : r.events ≠ []) :
    r.isProgressNotify = false := by
  cases hp : r.isProgressNotify
  · rfl
  · exact absurd (isProgressNotify_events hp) h

theorem isProgressNotify_false_of_created {r : RespModel} (h : r.created = true) :
    r.isProgressNotify = false := by
  unfold RespModel.isProgressNotify; simp [h]

/-- `Broadcast`'s premise on the response. -/
theorem watchCase_pre {pfx : GoString} {k k' : w64} {r : RespModel} (h : WatchCase pfx k k' r) :
    EvRevSorted r.events ∧ RespRevsBounded r := by
  obtain ⟨hh, hc | hc | hc⟩ := h
  · unfold RespRevsBounded; rw [hc.2.1]; exact ⟨List.Pairwise.nil, hh, fun e he => by cases he⟩
  · unfold RespRevsBounded; rw [isProgressNotify_events hc.1]
    exact ⟨List.Pairwise.nil, hh, fun e he => by cases he⟩
  · exact ⟨hc.2.1, hh, fun e he => (hc.2.2.1 e he).2⟩

/-- The new state after `Broadcast`: the writer's invariant, the stream continuing the watch
at the new cursor and at `rev - 1`. -/
theorem watchEvents_after (pfx : GoString) (cap : Nat) (c : DemuxCore) (r : RespModel)
    (k k' rev : w64) (hinv' : DemuxInv cap (updResp cap c r)) (hw : WriterOk pfx c)
    (hk : CursorOk pfx c k) (h0 : CursorOk pfx c (rev - W64 1))
    (hle : sint.Z (rev - W64 1) ≤ sint.Z k) (hcase : WatchCase pfx k k' r) :
    WriterOk pfx (updResp cap c r) ∧ CursorOk pfx (updResp cap c r) k' ∧
      CursorOk pfx (updResp cap c r) (rev - W64 1) ∧ sint.Z (rev - W64 1) ≤ sint.Z k' := by
  obtain ⟨-, hc | hc | hc⟩ := hcase
  · obtain ⟨hcr, hev, rfl⟩ := hc
    have hu : updResp cap c r = c := by
      unfold updResp; simp [isProgressNotify_false_of_created hcr, hev]
    rw [hu]; exact ⟨hw, hk, h0, hle⟩
  · obtain ⟨hp, hkp, rfl, hs⟩ := hc
    have hu : updResp cap c r = { c with maxRev := r.hdrRev } := by
      unfold updResp; simp [hp]
    rw [hu]
    have hl : ({ c with maxRev := r.hdrRev } : DemuxCore).lastRev = c.lastRev := rfl
    have ht := tailOk_step hk.2.2 hs
    refine ⟨fun _ => by rw [hl]; exact ht, ⟨hk.1, by simp only; have := hk.2.1; omega, ht⟩,
      h0, by omega⟩
  · obtain ⟨hne, -, hrevs, hlast⟩ := hc
    have hu : updResp cap c r = updCore cap c r.events := by
      unfold updResp; simp [isProgressNotify_false_of_events hne, hne]
    rw [hu] at hinv' ⊢
    obtain ⟨e, he, rfl⟩ : ∃ e, r.events.getLast? = some e ∧ e.rev = k' := by
      cases h : r.events.getLast? with
      | none => rw [h] at hlast; cases hlast
      | some e => rw [h] at hlast; exact ⟨e, rfl, Option.some.inj hlast⟩
    obtain ⟨b, hb, hbr⟩ := splitBatches_last_rev r.events e he
    have hl : (updCore cap c r.events).lastRev = sint.Z e.rev := by
      unfold DemuxCore.lastRev updCore
      simp only [List.getLast?_append, hb, Option.some_or, hbr]
    have hmax : (updCore cap c r.events).maxRev = e.rev := by
      unfold updCore; simp only [he]
    have hbase : (updCore cap c r.events).base = c.base := rfl
    have hmin : (updCore cap c r.events).minRev ≠ W64 0 := by
      intro h
      have hs := (hinv'.uninit h).1
      unfold updCore at hs
      simp only [List.append_eq_nil_iff, splitBatches_eq_nil_iff] at hs
      exact hne hs.2
    have hke : sint.Z k < sint.Z e.rev := (hrevs e (List.mem_of_getLast? he)).1
    refine ⟨fun _ => ?_, ⟨hmin, ?_, ?_⟩, ⟨hmin, ?_, ?_⟩, by omega⟩
    · rw [hl, hmax]; exact Or.inl (Int.le_refl _)
    · rw [hbase]; have := hk.2.1; omega
    · rw [hl]; exact Or.inl (Int.le_refl _)
    · rw [hbase]; exact h0.2.1
    · rw [hl]; exact Or.inl (by omega)

/-! ## Separation-logic lemmas -/

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem etcdStepCert_cert (pfx : GoString) :
    (etcdStepCert (GF := GF) pfx).cert = etcdStepCertBody pfx := rfl

theorem demuxWriter_inv (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF)
    (c : DemuxCore) :
    demuxWriter d γd cap C c ⊢ demuxWriter d γd cap C c ∗ ⌜DemuxInv cap c⌝ := by
  unfold demuxWriter
  iintro ⟨Hg, Hh, %Hi⟩
  iframe
  ipureintro; exact ⟨Hi, Hi⟩

/-- An exact chain from the watch: each batch certified from the previous one's revision. -/
theorem watchChain_certChain (pfx : GoString) (p : w64) (bs : List Batch) :
    watchChain (GF := GF) pfx p bs ⊢ certChain (etcdStepCert pfx) (sint.Z p) bs := by
  induction bs generalizing p with
  | nil => iintro _; iapply certChain_nil
  | cons b bs ih =>
    unfold watchChain
    rw [certChain_cons, etcdStepCert_cert]
    iintro ⟨#Hb, %Hlt, H⟩
    isplitl []
    · iexists p
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, Hlt⟩
      imodintro
      iexact Hb
    iapply ih (batchRev b) $$ H

/-- The watch's chain from the cursor `k` is a certificate chain from the stream's last batch
`last`, when nothing changed between `last` and `k` (`TailOk`) and the first batch is above
`last`. -/
theorem watchChain_certChain_tail (pfx : GoString) (last : Int) (k : w64) (bs : List Batch)
    (ht : TailOk pfx last k) (habove : ∀ b, bs.head? = some b → last < sint.Z (batchRev b)) :
    watchChain (GF := GF) pfx k bs ⊢ certChain (etcdStepCert pfx) last bs := by
  cases bs with
  | nil => iintro _; iapply certChain_nil
  | cons b bs =>
    have hab := habove b rfl
    unfold watchChain
    rw [certChain_cons, etcdStepCert_cert]
    iintro ⟨#Hb, %Hlt, H⟩
    isplitl []
    · rcases ht with hle | ⟨q, hq, hs⟩
      · iexists k
        isplitr
        · ipureintro; exact ⟨hle, hab⟩
        imodintro
        iexact Hb
      · iexists q
        isplitr
        · ipureintro; exact ⟨hq, hab⟩
        imodintro
        unfold etcdStepCertBody
        icases Hb with ⟨%cs, #Hm, %Hst⟩
        iexists cs
        iframe Hm
        ipureintro
        exact ⟨etcdStep_compose q k (batchRev b) pfx cs hs Hst.1, Hst.2⟩
    iapply watchChain_certChain pfx (batchRev b) bs $$ H

/-- etcd's watch contract for a response that is not an error: its pure part and the chain of
its batches from the cursor. -/
theorem watchRespOk_case (pfx : GoString) (k k' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v) :
    watchRespOk (GF := GF) pfx k k' v r ⊢
      ⌜WatchCase pfx k k' r⌝ ∗ watchChain pfx k (splitBatches r.events) := by
  unfold watchRespOk
  iintro ⟨%Hh, (%H | %H | %H | ⟨%H, #Hc⟩)⟩
  · exact absurd H.1 hne
  · isplitr
    · ipureintro; exact ⟨Hh, Or.inl H.2⟩
    rw [H.2.2.1]; unfold splitBatches watchChain; itrivial
  · isplitr
    · ipureintro; exact ⟨Hh, Or.inr (Or.inl H.2)⟩
    rw [isProgressNotify_events H.2.1]; unfold splitBatches watchChain; itrivial
  · isplitr
    · ipureintro; exact ⟨Hh, Or.inr (Or.inr H.2)⟩
    iexact Hc

/-- What `Broadcast` asks of the caller: the response's certificate, from the stream's state
`c` continuing the watch at the cursor `k`. -/
theorem watchEvents_respCert (pfx : GoString) (cap : Nat) (c : DemuxCore) (r : RespModel)
    (k k' : w64) (hinv : DemuxInv cap c) (hk : CursorOk pfx c k)
    (hcase : WatchCase pfx k k' r) :
    watchChain (GF := GF) pfx k (splitBatches r.events) ⊢
      ⌜c.minRev ≠ W64 0 ∧ validRevisions r c.maxRev = true⌝ -∗
        respCert (etcdStepCert pfx) c r := by
  iintro #Hc %Hv
  obtain ⟨-, hc | hc | hc⟩ := hcase
  · unfold respCert
    rw [isProgressNotify_false_of_created hc.1, hc.2.1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  · unfold respCert
    rw [hc.1]
    simp only [↓reduceIte]
    ipureintro
    have := hk.2.1
    omega
  · obtain ⟨hne, -, hrevs, -⟩ := hc
    unfold respCert
    rw [isProgressNotify_false_of_events hne]
    simp only [Bool.false_eq_true, ↓reduceIte, hne]
    have hvr := Hv.2
    unfold validRevisions at hvr
    rw [isProgressNotify_false_of_events hne] at hvr
    simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hvr
    iapply watchChain_certChain_tail pfx c.lastRev k _ hk.2.2 ?_ $$ Hc
    intro b hb
    obtain ⟨x, hx, hxr⟩ := splitBatches_rev_mem r.events b (List.mem_of_mem_head? hb)
    rw [← hxr]
    have hmx := hvr x hx
    have hkx := (hrevs x hx).1
    unfold DemuxCore.lastRev
    cases hl : c.stream.getLast? with
    | none => dsimp only; have := hk.2.1; omega
    | some b' =>
      dsimp only
      have := hinv.stream_le b' (List.mem_of_getLast? hl)
      omega

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.watchEvents.wp_proof
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithProgressNotify : WithProgressNotify.spec (GF := GF) (hG := hG))
    (wp_WithCreatedNotify : WithCreatedNotify.spec (GF := GF) (hG := hG))
    (wp_Init : demux.Init.spec (GF := GF) (hG := hG))
    (wp_Set : ready.Set.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG))
    (wp_Reset : ready.Reset.spec (GF := GF) (hG := hG))
    (wp_Broadcast : demux.Broadcast.spec (GF := GF) (hG := hG)) :
    Cache.watchEvents.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap rev aec γa Pa Ra arcv ro γo c0
  wp_start as ⟨#Hc, #Hae, Haec, #Honce, Hw, %Hrev, Ho⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  unfold isCacheFields
  iNamed Hc
  icases HisICtx with ⟨%ics, #Hctxi⟩
  ihave #Hctxi' := Hctxi
  iNamed Hctxi'
  imod monoNatLbOwn_0 (GF := GF) γr.epoch with #Hlb0
  wp_auto
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev rev as %f2 #Hf2
  wp_apply wp_WithProgressNotify as %f3 #Hf3
  wp_apply wp_WithCreatedNotify as %f4 #Hf4
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  generalize hsl : slice.mk sl _ _ = optsSl
  have hfs : (([f1, zero_val GoFunc, zero_val GoFunc, zero_val GoFunc].set
      (sint.nat (W64 (0 + 1))) f2).set (sint.nat (W64 (0 + 1 + 1))) f3).set
      (sint.nat (W64 (0 + 1 + 1 + 1))) f4 = [f1, f2, f3, f4] := rfl
  ihave #Hopts : optsAt optsSl ([withPrefixM, withRevM rev, withProgressNotifyM,
      withCreatedNotifyM] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · cases Hf; cases Hg; iexact Hf3
    · cases Hf; cases Hg; iexact Hf4
    · simp at Hf
  iunfold isEtcdWatcher at HisWatcher
  ihave #HW := HisWatcher $$ %cf.ictx %ics %cf.pfx %optsSl
    %([withPrefixM, withRevM rev, withProgressNotifyM, withCreatedNotifyM] : List (OpFull → OpFull))
    %rev
  wp_apply HW $$ [] as %wch %γw ⟨#Hwch, Hcons⟩
  · iframe Hctxi Hopts
    ipureintro
    exact ⟨(watchEvents_opts cf.pfx rev).1, (watchEvents_opts cf.pfx rev).2, Hrev⟩
  ipersist c
  ipersist readyOnce
  ipersist applyErr
  ipersist rev
  ipersist watchCh
  ihave HI : (∃ (k : w64) (n : Nat) (cc : DemuxCore),
      "Hcons" ∷ etcdWatchConsumer γw n k ∗ "Hw" ∷ cacheWriter cf γd cap cc ∗
      "Haec" ∷ spscConsumer γa arcv ∗ "%Hle" ∷ ⌜sint.Z (rev - W64 1) ≤ sint.Z k⌝ ∗
      "Ho" ∷ ((dghostVar γo (DFrac.own (1 : Qp).half) false ∗ ⌜k = rev - W64 1⌝) ∨
       (dghostVar γo DFrac.discard true ∗
         ⌜CursorOk cf.pfx cc k ∧ CursorOk cf.pfx cc (rev - W64 1)⌝)) : IProp GF)
    $$ [Hcons Hw Haec Ho]
  · iexists rev - W64 1, 0, c0
    simp only [named]
    iframe Hcons Hw Haec
    isplitr
    · ipureintro; exact Int.le_refl _
    icases Ho with (Ho | ⟨#Ho, %Hk⟩)
    · ileft; iframe Ho; try (ipureintro; rfl)
    · iright; iframe Ho; ipureintro; exact ⟨Hk, Hk⟩
  ihave #Hlb0' : readyEpochLb γr 0 $$ []
  · iunfold readyEpochLb; iexact Hlb0
  wp_for HI
  wp_apply +noauto HDone as %ch1 %γ1 #Hdone
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-c.internalCtx.Done()`: return `ctx.Err()`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    ihave #HErrU := HErr $$ %Broadcast.Unknown
    wp_apply HErrU as %err -
    wp_for_post
    iapply HΦ
    iexists cc
    iframe Hw
    icases Ho with (⟨Ho, -⟩ | ⟨Ho, %Hk⟩)
    · ileft; iexact Ho
    · iright; iframe Ho; ipureintro; exact Hk.2
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-watchCh`
    simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
      inferInstance, wch, γw.spsc.chanName
    isplit
    · ipureintro; rfl
    isplit
    · iunfold isEtcdWatchChan at Hwch; iunfold isSpsc at Hwch; icases Hwch with ⟨$, -⟩
    iapply etcdWatch_recv_au wch γw cf.pfx n k _ $$ Hwch [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok H
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with %Hv
      wp_auto
      wp_for_post
      iapply HΦ
      iexists cc
      iframe Hw
      icases Ho with (⟨Ho, -⟩ | ⟨Ho, %Hk⟩)
      · ileft; iexact Ho
      · iright; iframe Ho; ipureintro; exact Hk.2
    simp only [↓reduceIte]
    icases H with ⟨%r, %k', #Hr, #Hok, Hcons⟩
    wp_auto
    wp_apply Once.wp_Do_frame ro (dghostVar γo (DFrac.own (1 : Qp).half) false)
      (dghostVar γo DFrac.discard true)
      iprop(cacheWriter cf γd cap cc ∗
        ((dghostVar γo (DFrac.own (1 : Qp).half) false ∗ ⌜k = rev - W64 1⌝) ∨
         (dghostVar γo DFrac.discard true ∗
           ⌜CursorOk cf.pfx cc k ∧ CursorOk cf.pfx cc (rev - W64 1)⌝)))
      iprop(∃ c1, cacheWriter cf γd cap c1 ∗
        ⌜CursorOk cf.pfx c1 k ∧ CursorOk cf.pfx c1 (rev - W64 1)⌝) _
      $$ [$Honce Hw Ho] as ⟨#HQ, HR⟩
    · isplitl [Hw Ho]
      · iframe
      unfold onceFrameSpec
      iintro %Ψ ⟨HP, Hw, Ho⟩ HΨ
      icases Ho with (⟨Hh, %Hk⟩ | ⟨#Ht, -⟩)
      · imod dghostVar_update_halves true γo false false $$ HP Hh with ⟨H1, -⟩
        imod dghostVar_persist $$ H1 with #H1
        unfold cacheWriter
        icases Hw with ⟨Hdw, %Hwo⟩
        icases demuxWriter_inv $$ Hdw with ⟨Hdw, %Hinv⟩
        wp_auto
        wp_apply wp_Init cf.demux γd cap (etcdStepCert cf.pfx) cc rev $$ [$HisDemux $Hdw] as Hdw
        wp_apply wp_Set cf.ready γr 0 $$ [$HisReady $Hlb0'] as -
        iapply HΨ
        iframe H1
        iexists (initCore cc rev).1
        iframe Hdw
        have hi := initCore_ok cf.pfx cap cc rev Hinv Hwo Hrev
        subst Hk
        ipureintro; exact ⟨hi.2, hi.1, hi.1⟩
      · iexfalso
        ihave %H := dghostVar_agree $$ HP Ht
        cases H
    ihave Hst : (∃ c1, cacheWriter cf γd cap c1 ∗
        ⌜CursorOk cf.pfx c1 k ∧ CursorOk cf.pfx c1 (rev - W64 1)⌝ : IProp GF) $$ [HR]
    · icases HR with (H | ⟨Hw, (⟨Hh, -⟩ | ⟨-, %H⟩)⟩)
      · iexact H
      · iexfalso; ihave %H := dghostVar_agree $$ Hh HQ; cases H
      · iexists cc; iframe Hw; ipureintro; exact H
    icases Hst with ⟨%c1, Hw, %Hk1⟩
    wp_apply wp_Err resp_ptr v (DFrac.own 1) $$ [$resp] as %err ⟨resp, %Herr⟩
    cases err with
    | ok e =>
      -- `resp.Err() != nil`: reset `ready`, return the error
      wp_auto
      wp_apply wp_Reset cf.ready γr 0 $$ [$HisReady $Hlb0'] as -
      wp_for_post
      iapply HΦ
      iexists c1
      iframe Hw
      iright
      iframe HQ
      ipureintro; exact Hk1.2
    | nil =>
    have hnw : ¬ watchErr v := by
      have h := Herr.1 rfl
      unfold watchErr
      rintro (h' | h' | h') <;> simp_all
    icases watchRespOk_case cf.pfx k k' v r hnw $$ Hok with ⟨%Hcase, #Hch⟩
    unfold cacheWriter
    icases Hw with ⟨Hdw, %Hwo⟩
    icases demuxWriter_inv $$ Hdw with ⟨Hdw, %Hinv⟩
    ihave #Hcert := watchEvents_respCert cf.pfx cap c1 r k k' Hinv Hk1.1 Hcase $$ Hch
    wp_auto
    wp_apply wp_Broadcast cf.demux γd cap (etcdStepCert cf.pfx) c1 v r
      $$ [$HisDemux $Hdw $Hr $Hcert] as %berr Hb
    · ipureintro; exact watchCase_pre Hcase
    cases hb : broadcastCore cap c1 r with
    | none =>
      icases Hb with ⟨Hdw, %Hberr⟩
      obtain ⟨e, rfl⟩ := Hberr
      wp_auto
      wp_apply wp_Reset cf.ready γr 0 $$ [$HisReady $Hlb0'] as -
      wp_for_post
      iapply HΦ
      iexists c1
      iframe Hdw
      isplitr
      · ipureintro; exact Hwo
      iright
      iframe HQ
      ipureintro; exact Hk1.2
    | some c' =>
      have hc' : c' = updResp cap c1 r := by
        unfold broadcastCore at hb
        split at hb
        · cases hb
        split at hb
        · cases hb
        exact (Option.some.inj hb).symm
      subst hc'
      icases Hb with ⟨Hdw, %Hberr⟩
      subst Hberr
      icases demuxWriter_inv $$ Hdw with ⟨Hdw, %Hinv'⟩
      have ha := watchEvents_after cf.pfx cap c1 r k k' rev Hinv' Hwo Hk1.1 Hk1.2 Hle Hcase
      wp_auto
      wp_for_post
      iframe HΦ
      iexists k', n + 1, updResp cap c1 r
      simp only [named]
      iframe Hcons Hdw Haec
      isplitr
      · ipureintro; exact ha.1
      isplitr
      · ipureintro; exact ha.2.2.2
      iright
      iframe HQ
      ipureintro; exact ⟨ha.2.1, ha.2.2.1⟩
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-applyErr`: reset `ready`, return the error
    simp only [chan.blockingClausePre]
    iexists GoError, inferInstance, inferInstance, inferInstance, inferInstance, aec, γa.chanName
    isplit
    · ipureintro; rfl
    isplit
    · iunfold isSpsc at Hae; icases Hae with ⟨$, -⟩
    iapply spsc_rcv_au γa aec Pa Ra arcv _ $$ Hae [$Hlc1 $Hlc2] Haec
    inext
    iintro %v %ok -
    wp_auto
    wp_apply wp_Reset cf.ready γr 0 $$ [$HisReady $Hlb0'] as -
    wp_for_post
    iapply HΦ
    iexists cc
    iframe Hw
    icases Ho with (⟨Ho, -⟩ | ⟨Ho, %Hk⟩)
    · ileft; iexact Ho
    · iright; iframe Ho; ipureintro; exact Hk.2
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
