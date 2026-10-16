/- Lean-first (no Rocq counterpart). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.node__stepWithWaitOption
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType

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
fresh result channel (`propP`, `Handoff`), whose result is then awaited. `ctx` is
`Background()`, whose `Done()` is `nil`; `n.done` never fires. (Raft v3.7, stage R5: `m` is a
pointer, handed on for good; its type read by `m.GetType()`, a new callee, over the `msgIn` each
case of `stepArg` holds; a network message's type is not `MsgProp` by `NetMsgOk`.) -/
theorem node.stepWithWaitOption.wp_proof
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)) :
    node.stepWithWaitOption.spec (GF := GF) (hG := hG) := by
  intro γ id n m wait
  wp_start as ⟨#Hnode, Harg⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  unfold stepArg
  icases Harg with (Hnet | ⟨%Hw, %data, Hm, #Hent⟩ | ⟨%Hw, Hfwd⟩)
  · -- a message from the network: `recvc <- m`
    iunfold netP at Hnet
    icases Hnet with ⟨%st, Hm, %Hok, #Hab, #Hlb, Hcr, Htc⟩
    wp_auto
    wp_apply wp_GetType.1 $$ [Hm] as Hm
    · iexact Hm
    wp_if_destruct
    · exact absurd Hif (netStepTypes_ne_prop Hok.1)
    wp_apply +noauto context.wp_background_Done
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
        ipureintro; exact Hok
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
        nv.propc', γ.propc, ({ m' := m, result' := rch } : msgWithResult)
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hpropc
      iapply handshake_send_au γ.propc nv.propc' ({ m' := m, result' := rch } : msgWithResult)
        (propP γ) iprop(True) $$ [$Hlc1 $Hlc2 $Hlc3] Hpropc [Hm Hprod]
      · unfold propP
        ileft
        iexists data, γr
        iframe Hm Hent Hho Hprod
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
    iunfold fwdP at Hfwd
    icases Hfwd with ⟨%st, Hm, %Hty, #Hab⟩
    wp_auto
    wp_apply wp_GetType.1 $$ [Hm] as Hm
    · iexact Hm
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
        (propP γ) iprop(True) $$ [$Hlc1 $Hlc2 $Hlc3] Hpropc [Hm]
      · unfold propP
        iright
        isplitr
        · ipureintro; rfl
        iunfold fwdP
        iexists st
        iframe Hm Hab
        ipureintro; exact Hty
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
