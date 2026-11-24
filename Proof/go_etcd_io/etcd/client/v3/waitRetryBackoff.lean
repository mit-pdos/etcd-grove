/-
Proof of `Spec/go_etcd_io/etcd/client/v3/waitRetryBackoff.lean` (prove-ps2-wrb, 2026-11-22; until
then a trust-boundary axiom, the body untranslated): over the options' backoff function
(`retryOptsAt`), Perennial's `time.NewTimer` and `Timer.Stop`, the context's `Done()`/`Err()` in each
of `ctxOk`'s three cases, and `contextErrToGRPCErr`. Lean-first (no Rocq counterpart).

The `select` on `ctx.Done()` and the timer's channel: a quiet context's `Done()` (and a `ctxErrs`
context's, when nil) is the nil channel, whose case never fires; otherwise the case fires only once
the context is done (Perennial's model: `isContextDone_receive`; `ctxErrs`: the broadcast channel's
done flag at its internal names, `bcastInternal_recv`, which `ctxDoneCh` turns into
`ContextClosed`), when `Err()` returns a non-nil context error (`ctxErrLeaf`), which
`contextErrToGRPCErr` turns into a status error that is no handler's.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.waitRetryBackoff
public import Spec.go_etcd_io.etcd.client.v3.contextErrToGRPCErr
public import Proof.k8s_io.apimachinery.pkg.util.wait.BroadcastInternal
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem waitRetryBackoff.wp_proof
    (wp_ctxErr : contextErrToGRPCErr.spec (GF := GF) (hG := hG)) :
    waitRetryBackoff.spec (GF := GF) (hG := hG) := by
  intro ctx cd attempt o
  wp_start as ⟨#Hctx, #Hro⟩
  iunfold retryOptsAt at Hro
  icases Hro with ⟨%ov, #Ho, #Hbk⟩
  ihave ⟨-, -, #Hbf, -⟩ := options_fields_ro o ov $$ Ho
  -- `ctx.Done()`, in each of `ctxOk`'s cases: the nil channel, or one whose receive returns only
  -- once `ctx.Err()` returns a done context's error
  ihave #HD : iprop({{ True }} (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #()))
      {{ (ch : GoChan), RET #ch;
        ⌜ch = chan.nil⌝ ∨ ∃ γd : ChanNames, isChan ch γd Unit ∗
          □ ∀ Φr : Unit → Bool → IProp GF,
            (({{ True }} (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #()))
                {{ (err : GoInterface), RET #err; ctxErrLeaf err }}) -∗
              Φr () false) -∗
            recvAu γd Unit Φr }}) $$ []
  · iunfold ctxOk at Hctx
    icases Hctx with ⟨(#Hic | #Hq | #He), -⟩
    · -- Perennial's context model
      iintro !> %Φ - HΦ
      unfold context.isContext context.isContextDef
      iNamed Hic
      iapply HDone $$ []
      · itrivial
      inext
      iintro %ch %γch #Hdn
      iapply HΦ
      iright
      iexists γch
      isplitr
      · iapply context.isContextDone_is_chan $$ Hdn
      iintro !> %Φr HΦr
      iapply context.isContextDone_receive $$ Hdn
      iintro ⟨-, #Hcl⟩
      iapply HΦr
      iintro !> %Ψ - HΨ
      ihave #HE := HErr $$ %Broadcast.Done
      iapply HE $$ Hcl
      inext
      iintro %err %Hne Hce
      rw [ite_cond_eq_false _ _ (eq_false Hne)]
      iapply HΨ
      iapply ctxErrLeaf_of_isCtxErr $$ Hce
    · -- a quiet context: `Done()` is `nil`
      iunfold ctxQuiet at Hq
      icases Hq with ⟨#HDq, -, -⟩
      iintro !> %Φ - HΦ
      iapply HDq
      inext
      iapply HΦ
      ileft; ipureintro; rfl
    · -- a context following Go's contract (`ctxErrs`)
      iunfold ctxErrs at He
      icases He with ⟨#HDe, #HEe, -, -⟩
      iunfold ctxDone at HDe
      iintro !> %Φ - HΦ
      iapply HDe
      inext
      iintro %ch #Hch
      iapply HΦ
      iunfold ctxDoneCh at Hch
      icases Hch with (%Hn | ⟨%γ, %γi, %Q, #Hint, #Hw⟩)
      · ileft; ipureintro; exact Hn
      iright
      iexists γ
      isplitr
      · iapply isBroadcastChanInternal_is_chan $$ Hint
      iintro !> %Φr HΦr
      iapply bcastInternal_recv ch γ γi Q $$ Hint
      iintro #Hdn
      iapply HΦr
      iintro !> %Ψ - HΨ
      ihave #Hcl := Hw $$ Hdn
      iunfold ctxErrsErr at HEe
      iapply HEe $$ %Broadcast.Done %Ψ Hcl
      inext
      iintro %err %Hne %- #Hs #Hcell Hm
      iapply HΨ
      iapply ctxErrLeaf_of_errs err Hne $$ [Hm]
      iframe Hs Hcell Hm
  ihave #Hbt : iprop({{ True }} (App (Val #ov.backoffFunc') (Val #attempt))
      {{ (d : w64), RET #d; True }}) $$ []
  · iintro !> %Φ' - HΦ'
    iunfold optionsOk at Hbk
    iunfold go_etcd_io.etcd.cache.v3.backoffOk at Hbk
    iapply Hbk
    inext
    iintro %d
    iapply HΦ'
    itrivial
  wp_auto
  wp_if_destruct
  rotate_left
  · -- `attempt == 0`: no wait
    (try wp_auto)
    iapply HΦ
    isplitl
    · iapply clientErrOk_nil
    ileft; ipureintro; rfl
  (try wp_auto)
  wp_apply Hbt as %d -
  (try wp_auto)
  wp_if_destruct
  rotate_left
  · -- no wait
    (try wp_auto)
    iapply HΦ
    isplitl
    · iapply clientErrOk_nil
    ileft; ipureintro; rfl
  wp_apply time.wp_NewTimer as %t %tc %γt #Ht
  ihave #Ht' := Ht
  iunfold time.isTimer at Ht'
  icases Ht' with ⟨#HtC, -, -, #HtB⟩
  wp_apply (lc := 2) HD as %ch Hch
  (try wp_auto)
  icases Hch with (%Hnil | ⟨%γd, #Hdc, #Hrecv⟩)
  · -- the nil channel: only the timer fires
    subst Hnil
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · iright; iapply chan.nilClausePre_recv Unit _ _ rfl
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance,
        tc, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ HtB
      iapply bag_recv_au γt tc _ _ $$ [$Hlc1 $Hlc2] HtB
      inext
      iintro %tm -
      (try wp_auto)
      iapply HΦ
      isplitl
      · iapply clientErrOk_nil
      ileft; ipureintro; rfl
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-ctx.Done()`: the context is done
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γd
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hdc
      iapply Hrecv
      iintro #HErr
      (try wp_auto)
      wp_apply time.Timer.wp_Stop_timer t tc γt $$ Ht as %b -
      (try wp_auto)
      wp_apply HErr as %err #Hel
      wp_apply wp_ctxErr $$ [Hel] as %err' ⟨#Hok, #Hnh, -⟩
      · iframe #
      (try wp_auto)
      iapply HΦ
      iframe Hok
      iright; iexact Hnh
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-timer.C`
      simp only [chan.blockingClausePre]
      iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance,
        tc, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ HtB
      iapply bag_recv_au γt tc _ _ $$ [$Hlc1 $Hlc2] HtB
      inext
      iintro %tm -
      (try wp_auto)
      iapply HΦ
      isplitl
      · iapply clientErrOk_nil
      ileft; ipureintro; rfl
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
