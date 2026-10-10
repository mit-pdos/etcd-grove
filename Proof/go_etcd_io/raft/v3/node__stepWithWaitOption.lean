/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__stepWithWaitOption

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
variable [AllG GF]

/-- A message from the network goes onto `recvc` (`netP`); a proposal onto `propc` with a
fresh result channel (`propP`, `Handoff`), whose result is then awaited. `ctx` is
`Background()`, whose `Done()` is `nil`; `n.done` never fires. -/
theorem node.stepWithWaitOption.wp_proof :
    node.stepWithWaitOption.spec (GF := GF) (hG := hG) := by
  intro γ id n m wait
  wp_start as ⟨#Hnode, Harg⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  unfold stepArg
  icases Harg with (⟨%Hty, Hnet⟩ | ⟨%Hw, %data_sl, %esl, %data, %Hm, Hes, Hcap, #Hdata, #Hent⟩ | ⟨%Hw, Hfwd⟩)
  · -- a message from the network: `recvc <- m`
    wp_auto
    wp_if_destruct
    · exact absurd Hif Hty
    wp_apply +noauto context.wp_background_Done
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists raftpb.Message, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.recvc', γ.recvc, m
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hrecvc
      iapply handshake_send_au γ.recvc nv.recvc' m (netP γ id) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hrecvc Hnet
      inext
      iintro -
      wp_auto
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · iright
      iapply chan.nilClausePre_recv Unit _ _ rfl
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
    subst Hw Hm
    wp_auto
    wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %rch %γrc ⟨#Hrch, %_, Hoc⟩
    · ipureintro; decide
    ihave Hoc : ownChan γrc GoInterface (.Buffered []) $$ Hoc
    imod start_handoff rch (fun (_ : GoInterface) => iprop(True)) iprop(True) iprop(True) γrc
      $$ Hrch Hoc with ⟨%γr, %Hγr, #Hho, Hprod, Hcons⟩
    subst Hγr
    wp_apply +noauto context.wp_background_Done
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists msgWithResult, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.propc', γ.propc, ({ m' := propMsg esl, result' := rch } : msgWithResult)
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hpropc
      iapply handshake_send_au γ.propc nv.propc' ({ m' := propMsg esl, result' := rch } : msgWithResult)
        (propP γ) iprop(True) $$ [$Hlc1 $Hlc2 $Hlc3] Hpropc [Hes Hcap Hprod]
      · unfold propP
        ileft
        iexists data_sl, esl, data, γr
        iframe Hes Hcap Hdata Hent Hho Hprod
        ipureintro; rfl
      inext
      iintro -
      wp_auto
      wp_apply +noauto context.wp_background_Done
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
        iintro %v %ok -
        wp_auto
        cases v <;> wp_auto <;> (iapply HΦ; itrivial)
      iapply BigAndL.bigAndL_cons.2
      isplit
      · iright
        iapply chan.nilClausePre_recv Unit _ _ rfl
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
    · iright
      iapply chan.nilClausePre_recv Unit _ _ rfl
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
    ihave %Hty : ⌜m.Type' = MsgProp⌝ $$ [Hfwd]
    · unfold fwdP
      icases Hfwd with ⟨%H, -⟩
      ipureintro; exact H
    wp_auto
    wp_if_destruct
    rotate_left
    · exact absurd Hty Hif
    wp_apply +noauto context.wp_background_Done
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
        (propP γ) iprop(True) $$ [$Hlc1 $Hlc2 $Hlc3] Hpropc [Hfwd]
      · unfold propP
        iright
        isplitr
        · ipureintro; rfl
        iexact Hfwd
      inext
      iintro -
      wp_auto
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · iright
      iapply chan.nilClausePre_recv Unit _ _ rfl
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
