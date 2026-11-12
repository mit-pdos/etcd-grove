/-
The proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/compactor__runWatchLoop.lean` (Q1 (b) of
`notes/k8s-compactor-plan.md`). Lean-first.

The loop runs under `wait.ContextForChannel(stop)`: a context the client's `Get` takes (`ctxOk`,
`chanCtx_ok`) and one its `Watch` takes (`watchCtx`, `chanCtx_watch`, at a fresh Done cell). Each
iteration waits on `time.After` or the stop channel (`wp_select_bag_stop`), reads the key
(`getCompactRev`), records its revision, watches the key from the revision read with the caller's
read update (`keyReadOk`: each response's state has `keyHistOk`) and records each response's
revision (`fromWatchResponse`, whose premise `respKeyOk_of_state` gives). The inner loop's
invariant is the watch channel's consumer state alone.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__runWatchLoop
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__getCompactRev
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__fromWatchResponse
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__UpdateCompactRevision
public import Spec.k8s_io.apimachinery.pkg.util.wait.ContextForChannel
public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Done
public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Err
public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Deadline
public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Value
public import Spec.k8s_io.klog.v2.Errorf
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Perennial.Spec.time.After
public import Proof.go_etcd_io.etcd.client.v3.ChanWatchCtx
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.LoopSelect
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchKey
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [ctxDescs : EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- The watch of the key from `cur`: its operation (`compact_rev_key` alone, from `cur`). -/
abbrev keyWatchOp (cur : w64) : OpFull :=
  (opWatchModel compactRevKey [withRevM cur]).watchNorm

theorem keyWatchOp_key (cur : w64) : (keyWatchOp cur).key = compactRevKey := by
  simp [keyWatchOp, OpFull.watchNorm, opWatchModel, opFold, OpFull.getInit, withRevM,
    OpFull.newOp, OpModel.zero, compactRevKey]

theorem keyWatchOp_rangeEnd (cur : w64) : (keyWatchOp cur).base.rangeEnd = [] := by
  simp [keyWatchOp, OpFull.watchNorm, opWatchModel, opFold, OpFull.getInit, withRevM,
    OpFull.newOp, OpModel.zero, compactRevKey]

/-- **`cl.Watch(ctx, key, opts...)` by a client whose `Watcher` field is the `*watcher` `w`**
(`watcher.Watch.spec` through the field). -/
theorem client_Watch_field (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (cl w : Loc) (V : client.WEnv GF) (γ : KVNames) (ctx : GoInterfaceOk)
    (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF) (n : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isPkgInit (PROP := IProp GF) pkg_id.context ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"Watcher" cl ↦□
          GoInterface.ok (client.watcherIfaceOf w) ∗
        client.isClientWatcher V w ∗ ⌜V.kst = γ.st⌝ ∗
        EtcdGrove.context.watchCtx ctx cd ∗ optsAt sl opts ∗
        ⌜(opWatchModel key opts).isRangeWatch rev = true ∧ ¬ opWatchPanics key opts ∧
          1 ≤ sint.Z rev ∧ watchSizeOk (opWatchModel key opts)⌝ ∗
        □ (⌜V.nm = 1 ∧ 0 < n⌝ → auth.authPubLbM (V.mem 0).2.E.authMode n) ∗
        □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γ σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
    {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
        isSpsc γw.spsc ch (watchStateElem V.kv γw (opWatchModel key opts).watchNorm Q
          iprop(□ (⌜V.nm = 1⌝ → client.watchCheckOk (V.mem 0).2.tag (V.mem 0).2.s V.conn
            (GoInterface.ok ctx) n (opWatchModel key opts).key
            (opWatchModel key opts).base.rangeEnd)))
          (fun _ => iprop(True)) ∗
        spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListIdxOwn γw.cur 0 (rev - W64 1) }} := by
  iintro %Φ ⟨#P1, #P2, #P3, #Hwf, #Hw, %Hk, #Hctx, #Hopts, %Hpre, #Hauth, #Hau⟩ HΦ
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Watch_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_Watch w V γ ctx cd key sl opts rev Q n) $$ [] as %ch %γw H
  · iframe #
    ipureintro; exact ⟨Hk, Hpre⟩
  iapply HΦ $$ H

/-- See the file header. -/
theorem compactor.runWatchLoop.wp_proof
    (wp_ContextForChannel : wait.ContextForChannel.spec (GF := GF) (hG := hG))
    (wp_Done : wait.channelContext.Done.spec (GF := GF) (hG := hG))
    (wp_Err : wait.channelContext.Err.spec (GF := GF) (hG := hG))
    (wp_Deadline : wait.channelContext.Deadline.spec (GF := GF) (hG := hG))
    (wp_Value : wait.channelContext.Value.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_getCompactRev : compactor.getCompactRev.spec (GF := GF) (hG := hG))
    (wp_UpdateCompactRevision : compactor.UpdateCompactRevision.spec (GF := GF) (hG := hG))
    (wp_WithRev : EtcdGrove.WithRev.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_fromWatchResponse : compactor.fromWatchResponse.spec (GF := GF) (hG := hG))
    (wp_Endpoints : EtcdGrove.Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_Errorf : klog.Errorf.spec (GF := GF) (hG := hG)) :
    compactor.runWatchLoop.spec (GF := GF) (hG := hG) := by
  intro _ _ c cl eps V γk recorded γc sc γs
  wp_start as ⟨#Hc, #Hstop, #Hcl, #Hko, #Hwo, #Hkr⟩
  rw [show k8s_io.apiserver.pkg.storage.etcd3.compactRevKey = #compactRevKey from rfl]
  ihave #Hc' := Hc
  iunfold compactorCore at Hc'
  icases Hc' with ⟨%Hpers, #Hclf, -, -, -, -, -⟩
  iunfold compactorChanOk at Hstop
  icases Hstop with ⟨#Hsc, #Hbc⟩
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc with ⟨%γi, #Hint, -⟩
  ihave #Pw : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait $$ []
  · iPkgInit
  ihave #Pklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave ⟨#Hctx, #Hce⟩ := chanCtx_ok wp_Done wp_Err wp_Deadline wp_Value EtcdGrove.rpctypesEtcdError_asTarget sc γs γi iprop(True)
    $$ [Pw Hint]
  · iframe #
  imod chanCtx_watch wp_Done wp_Err wp_Value sc γs γi $$ [Pw Hint] with ⟨%γdn, #Hwctx⟩
  · iframe #
  iunfold clientWatchOk at Hwo
  icases Hwo with ⟨%w, %Vw, #Hwf, #Hcw, %Hkst⟩
  ihave #Hcl' := Hcl
  iunfold isNewClient at Hcl'
  icases Hcl' with ⟨-, #Hrco, -, -⟩
  (try wp_auto)
  wp_apply wp_ContextForChannel sc
  (try wp_auto)
  ipersist c
  ipersist ctx
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  (try wp_auto)
  wp_apply (lc := 2) (wp_After _) as %ach %γach #Hbag
  (try wp_auto)
  wp_apply (wp_Done sc) $$ [$Pw]
  (try wp_auto)
  wp_apply_core (wp_select_bag_stop ach γach sc γs iprop(True)) $$ Hbag Hbc [$Hlc1 $Hlc2]
  isplit
  · iintro %t
    (try wp_auto)
    wp_apply (wp_getCompactRev c cl γk recorded γc (chanCtxVal sc) (chanCd γi)) $$ []
      as %cr %cur %err Hout
    · iframe #
    icases Hout with (%Herr | ⟨%Hok, #Hrec⟩)
    · -- the read failed: logged, the next iteration
      cases err with
      | nil => exact absurd rfl Herr
      | ok ei =>
      (try wp_auto)
      wp_apply wp_Endpoints cl $$ [] as %esl ⟨%eps', Hesl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl -
      (try wp_auto)
      wp_apply wp_Errorf _ _ $$ []
      (try wp_auto)
      wp_for_post
      iframe
    obtain ⟨rfl, hcur⟩ := Hok
    (try wp_auto)
    wp_apply (wp_UpdateCompactRevision c cl γk recorded γc cr) $$ [] as -
    · iframe #
    (try wp_auto)
    -- the watch's option, `WithRev(currentRev)`
    wp_apply wp_WithRev cur as %f #Hf
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    ipersist Hosl
    (try wp_auto)
    generalize hosl : slice.mk osl _ _ = optsSl
    ihave #Hopts : optsAt optsSl ([withRevM cur] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hosl
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f' %g %Hf' %Hg
      rcases i with _ | i
      · cases Hf'; cases Hg; iexact Hf
      · simp at Hf'
    iunfold keyReadOk at Hkr
    iunfold kvReadAu at Hkr
    iunfold kvAu at Hkr
    wp_apply (client_Watch_field wp_Watch cl w Vw γk (chanCtxVal sc)
        (_root_.Perennial.context.cdesc ⟨γdn, γi.doneGn⟩ iprop(True)) compactRevKey optsSl
        [withRevM cur] cur (keyHistOk γk recorded) 0) $$ [] as %wch %γw ⟨#Hsp, Hcons, -⟩
    · iframe #
      isplitr
      · ipureintro; exact Hkst
      isplitr
      · ipureintro
        refine ⟨?_, ?_, hcur, ?_⟩
        · simp [opWatchModel, opFold, OpFull.getInit, withRevM, OpFull.isRangeWatch, OpFull.newOp,
            OpModel.zero, compactRevKey]
        · simp [opWatchPanics, OpFull.watchPanics, opWatchModel, opFold, OpFull.getInit, withRevM,
            OpFull.newOp, OpModel.zero, compactRevKey]
        · unfold watchSizeOk
          simp [opWatchModel, opFold, OpFull.getInit, withRevM, OpFull.newOp, OpModel.zero,
            compactRevKey]
      iintro !> %h
      exact absurd h.2 (Nat.lt_irrefl 0)
    (try wp_auto)
    ihave HJ : (∃ (rs : List go_etcd_io.etcd.client.v3.WatchResponse)
        (v0 : go_etcd_io.etcd.client.v3.WatchResponse),
        "Hcons" ∷ spscConsumer γw.spsc rs ∗ "resp" ∷ resp_ptr ↦ v0 : IProp GF) $$ [Hcons resp]
    · iexists [], _; iframe
    wp_for HJ
    wp_apply (wp_spsc_receive (t := go_etcd_io.etcd.client.v3.WatchResponse.ty) γw.spsc wch _ _ rs)
      $$ [$Hsp $Hcons] as %v %ok Hv
    cases ok
    · -- the watch's channel closed: the next iteration
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      wp_for_post
      iframe
    simp only [↓reduceIte]
    icases Hv with ⟨HP, Hcons⟩
    unfold watchStateElem
    icases HP with ⟨%r, %σ, %c0, %c1, #Hr, #HQ, -, -, #Hok, -, -⟩
    ihave #Hrk := respKeyOk_of_state γk recorded (keyWatchOp cur) (keyWatchOp_key cur)
      (keyWatchOp_rangeEnd cur) σ c0 c1 v r $$ [Hr HQ Hok]
    · iframe #
    (try wp_auto)
    wp_apply (wp_fromWatchResponse c γk recorded v) $$ [] as %cr' %err' Hout'
    · iframe #
    icases Hout' with (%Herr' | ⟨%Hok', #Hrec'⟩)
    · cases err' with
      | nil => exact absurd rfl Herr'
      | ok ei =>
      (try wp_auto)
      wp_apply wp_Endpoints cl $$ [] as %esl ⟨%eps', Hesl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl -
      (try wp_auto)
      wp_apply wp_Errorf _ _ $$ []
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, _
      iframe
    subst Hok'
    (try wp_auto)
    wp_apply (wp_UpdateCompactRevision c cl γk recorded γc cr') $$ [] as -
    · iframe #
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, _
    iframe
  · (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end k8s
end EtcdGrove
end Perennial
