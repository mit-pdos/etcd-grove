/- Lean-first (no Rocq counterpart). -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.node__stepWithWaitOption
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.context.ErrDone

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A message from the network goes onto `recvc` (`netP`); a proposal onto `propc` with a
fresh result channel (`propP`, `Handoff`), whose result, `raft.Step`'s error for the proposal
(`stepErr`, stage R7c), is then awaited. `n.done` never fires.
`ctx` is any `nodeCtx` (stage R7a, `InvNodeCtx.lean`): its `Done()` is `nil` (the case never
fires) or a context's channel, from which a receive returns once the context is done, and the
call returns `ctx.Err()` (`nodeDone_recv_clause`, `isContext_Err_done` over the trust-boundary
spec `context.ErrDone`, a callee since stage R7c: the error is `Canceled` or `DeadlineExceeded`);
in the last `select` the proposal's result is then abandoned (the handoff's consumer token
dropped; `run` still sends and closes). (Raft v3.7, stage R5: `m` is a pointer, handed on for
good; its type read by `m.GetType()`, a new callee, over the `msgIn` each case of `stepArg` holds;
a network message's type is not `MsgProp` by `NetMsgOk`.) -/
theorem node.stepWithWaitOption.wp_proof
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (hED : context.ErrDone.spec (GF := GF) (hG := hG)) :
    node.stepWithWaitOption.spec (GF := GF) (hG := hG) := by
  intro γ id n m wait ctx cd
  wp_start as ⟨#Hnode, #Hctx, Harg⟩
  ihave #Hpctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hnode' := Hnode
  open_node Hnode'
  unfold stepArg
  icases Harg with (Hnet | ⟨%Hw, %data, Hm, #Hent, Htk⟩ | ⟨%Hw, Hfwd⟩)
  · -- a message from the network: `recvc <- m`
    iunfold netP at Hnet
    icases Hnet with ⟨%st, Hm, %Hok, %Hpvb, #Hab, #Hlb, Hcr, Htc⟩
    wp_auto
    wp_apply wp_GetType.1 $$ [Hm] as Hm
    · iexact Hm
    wp_if_destruct
    · exact absurd Hif (netStepTypes_ne_prop Hok.1)
    wp_apply +noauto nodeCtx_Done ctx cd $$ [$Hctx] as %dch #Hd
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.recvc', γ.recvc, m
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hrecvc
      iapply handshake_send_au γ.recvc nv.recvc' m (netP γ id) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hrecvc [Hm Hcr Htc]
      · iunfold netP
        iexists st
        iframe Hm Hab Hlb Hcr Htc
        ipureintro; exact ⟨Hok, Hpvb⟩
      inext
      iintro -
      wp_auto
      iapply HΦ
      iapply waitErr_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `case <-ctx.Done(): return ctx.Err()`
      iapply nodeDone_recv_clause ctx cd dch _ _ $$ Hd
      iintro ⟨#Hctx', #HPD, #HCC⟩
      wp_auto
      wp_apply isContext_Err_done hED ctx cd $$ [$Hpctx $Hctx' $HPD $HCC] as %cerr #Hcerr
      iapply HΦ
      iapply waitErr_ctx $$ Hcerr
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- a proposal: `propc <- pm`, then `<-pm.result`
    subst Hw
    wp_auto
    wp_apply wp_GetType.1 $$ [Hm] as Hm
    · iexact Hm
    wp_if_destruct
    rotate_left
    · exact absurd rfl Hif
    wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %rch %γrc ⟨#Hrch, %_, Hoc⟩
    · ipureintro; decide
    ihave Hoc : ownChan γrc GoInterface (.Buffered []) $$ Hoc
    imod start_handoff rch stepErr iprop(True) iprop(True) γrc
      $$ Hrch Hoc with ⟨%γr, %Hγr, #Hho, Hprod, Hcons⟩
    subst Hγr
    wp_apply +noauto nodeCtx_Done ctx cd $$ [$Hctx] as %dch #Hd
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists msgWithResult, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.propc', γ.propc, ({ m' := m, result' := rch } : msgWithResult)
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hpropc
      iapply handshake_send_au γ.propc nv.propc' ({ m' := m, result' := rch } : msgWithResult)
        (propP γ) iprop(True) $$ [$Hlc1 $Hlc2 $Hlc3] Hpropc [Hm Htk Hprod]
      · unfold propP
        ileft
        iexists data, γr
        iframe Hm Hent Htk Hho Hprod
      inext
      iintro -
      wp_auto
      wp_apply +noauto nodeCtx_Done ctx cd $$ [$Hctx] as %dch2 #Hd2
      wp_auto_lc 3
      wp_apply_core chan.wp_select_blocking_nil
      iapply BigAndL.bigAndL_cons.2
      isplit
      · ileft
        simp only [chan.blockingClausePre]
        iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance,
          rch, γr.chanName
        isplitr
        · ipureintro; rfl
        isplitr
        · unfold isHandoff
          icases Hho with ⟨$, -⟩
        iapply handoff_rcv_au γr rch _ _ _ false $$ Hho Hlc1 Hcons
        inext
        iintro %v %ok ⟨-, Hgot⟩
        unfold handoffGot
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases ok
        · -- the channel closed without a value: `run` always sends first, but the handoff's
          -- consumer, which never took the value, is only promised `Wc` (`True`); the zero
          -- value is `nil`
          simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hgot with ⟨%Hv, -⟩
          subst Hv
          wp_auto
          iapply HΦ
          iapply propErr_nil
        · simp only [↓reduceIte]
          icases Hgot with ⟨#Hse, -⟩
          cases v with
          | nil =>
            wp_auto
            iapply HΦ
            iapply propErr_nil
          | ok e =>
            wp_auto
            iapply HΦ
            iapply propErr_of_stepErr $$ Hse
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- `case <-ctx.Done(): return ctx.Err()`, the result abandoned
        iapply nodeDone_recv_clause ctx cd dch2 _ _ $$ Hd2
        iintro ⟨#Hctx', #HPD, #HCC⟩
        wp_auto
        wp_apply isContext_Err_done hED ctx cd $$ [$Hpctx $Hctx' $HPD $HCC] as %cerr #Hcerr
        iapply HΦ
        iapply propErr_of_nodeErr
        iapply nodeErr_ctx $$ Hcerr
      iapply BigAndL.bigAndL_cons.2
      isplit
      · ileft
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hdone
        iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc2 $Hlc3] Hdone
      iapply BigAndL.bigAndL_nil.2
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `case <-ctx.Done(): return ctx.Err()`
      iapply nodeDone_recv_clause ctx cd dch _ _ $$ Hd
      iintro ⟨#Hctx', #HPD, #HCC⟩
      wp_auto
      wp_apply isContext_Err_done hED ctx cd $$ [$Hpctx $Hctx' $HPD $HCC] as %cerr #Hcerr
      iapply HΦ
      iapply propErr_of_nodeErr
      iapply nodeErr_ctx $$ Hcerr
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial

  · -- a forwarded proposal (2026-10-10): `propc <- pm`, no result channel
    subst Hw
    iunfold fwdP at Hfwd
    icases Hfwd with ⟨%st, Hm, %Hty, #Hab, Htk⟩
    wp_auto
    wp_apply wp_GetType.1 $$ [Hm] as Hm
    · iexact Hm
    wp_if_destruct
    rotate_left
    · exact absurd Hty Hif
    wp_apply +noauto nodeCtx_Done ctx cd $$ [$Hctx] as %dch #Hd
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists msgWithResult, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.propc', γ.propc, ({ m' := m, result' := zero_val GoChan } : msgWithResult)
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hpropc
      iapply handshake_send_au γ.propc nv.propc' ({ m' := m, result' := zero_val GoChan } : msgWithResult)
        (propP γ) iprop(True) $$ [$Hlc1 $Hlc2 $Hlc3] Hpropc [Hm Htk]
      · unfold propP
        iright
        isplitr
        · ipureintro; rfl
        iunfold fwdP
        iexists st
        iframe Hm Hab Htk
        ipureintro; exact Hty
      inext
      iintro -
      wp_auto
      iapply HΦ
      iapply nodeErr_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `case <-ctx.Done(): return ctx.Err()`
      iapply nodeDone_recv_clause ctx cd dch _ _ $$ Hd
      iintro ⟨#Hctx', #HPD, #HCC⟩
      wp_auto
      wp_apply isContext_Err_done hED ctx cd $$ [$Hpctx $Hctx' $HPD $HCC] as %cerr #Hcerr
      iapply HΦ
      iapply nodeErr_ctx $$ Hcerr
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
