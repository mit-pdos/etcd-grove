/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__onStop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__onStop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.onStop.wp_proof :
    raftNode.onStop.spec (GF := GF) (hG := hG) := by
  intro E γ r Hwco
  wp_start as ⟨#Hr, Hdone, HST, Hrun, Hwt, Hwst, Hwap, ⟨%S, %p, %L, %sent, HrS, Hwvo, Hprod, #Hidx, %Ha0, #HcL⟩,
    ⟨%stm, %cid, #Hstm, Hmeta, Hpurge⟩⟩
  iunfold isRaftNode at Hr
  iNamed Hr
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, -, -, -, -, -, #HStop, -⟩
  subst Hnieq
  iunfold isRNTicker at Htki
  icases Htki with ⟨%c, #Hc, #Hcc, #HtkStop⟩
  iunfold isRNTransport at Htri
  icases Htri with ⟨%ti, %Htieq, #HSend, #HTrStop⟩
  subst Htieq
  ihave %Hsok := isWalStorage_ok st $$ Hsti
  obtain ⟨si, Hsieq⟩ := Hsok
  iunfold rnWalTok at Hwt
  icases Hwt with ⟨%st', #Hst', Hwo⟩
  icombine Hst Hst' gives %Hsteq
  have Hsteq' : st' = st := by first | exact Hsteq.symm | exact Hsteq.2.symm
  subst Hsteq'
  icombine Hst Hstm gives %Hsteq2
  have Hsteq2' : stm = st' := by first | exact Hsteq2.symm | exact Hsteq2.2.symm
  subst Hsteq2'
  iunfold rnWalView at Hwvo
  icases Hwvo with ⟨Hwv, Hwok⟩
  -- (R2b-1 stage 6) the records, taken out of the durability invariant (`rnDur_take`)
  imod rnDur_take γ.node.cl γ.wal (storage.walOf stm) _ rfl $$ Hdur Hwst Hwap Hwv Hwok
    with ⟨%σ, Hrecs, %Hσ, #Hσc⟩
  iunfold rnDoneTok at Hdone
  icases Hdone with ⟨%dnc', %st2, #Hdnc', #Hst2, Hbc⟩
  icombine Hdnc Hdnc' gives %Heq
  subst Heq
  icombine Hst Hst2 gives %Hsteq3
  have Hsteq3' : stm = st2 := by first | exact Hsteq3 | exact Hsteq3.2
  subst Hsteq3'
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Stop")]
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Stop")]
  wp_auto
  wp_apply HStop $$ [$Hrun] as ⟨-, Hvac⟩
  wp_apply HtkStop
  wp_apply HTrStop $$ [$HST]
  ihave #HClose := walClose_spec stm si Hsieq σ γ.id cid true $$ Hsti
  subst Hsieq
  wp_apply HClose $$ [$Hwo $Hrecs $Hmeta $Hpurge] as %cerr Hcerr
  · ipureintro; omega
  icases Hcerr with (⟨%hcerr, Hfiles⟩ | %Hcerr)
  rotate_left
  · exact absurd Hwco Hcerr
  subst hcerr
  (try wp_auto)
  -- (R2b-3b) the stop's escrow, with the image: the id vacant, the durable state, the files
  imod inv_alloc rnStopN ⊤ iprop(rnStopImage γ (storage.walOf (GoInterface.ok si)) ∨ token γ.sc)
    $$ [Hvac HrS Hfiles Hprod] with #Hesc
  · inext
    ileft
    iunfold rnStopImage
    iframe Hvac
    iexists S, σ, sent, L
    iframe HrS Hprod Hidx Hσc
    isplitl [Hfiles]
    · iunfold rnWalClosedW; iexists cid; iframe Hfiles
    obtain ⟨Hh, Hb, Hc, Hhs, Hag⟩ := Hσ
    isplitr
    · ipureintro
      have Hb' := Hb
      simp only [srvLE_length] at Hb' Hc
      refine ⟨Hh, ?_, ?_, ?_⟩
      · simpa [List.length_append] using Hb'
      · simpa [List.length_append] using Hc
      · -- (S1) `σ.commit` is the view's hard state's (`rnDur_take`'s `σ.hs = v.hs`)
        unfold StorContents.commit; rw [Hhs]; exact Ha0
    -- (S1) the committed log: the handed log, which the records' durable log agrees with
    iexists (srvLE γ.srv L)
    iframe HcL
    ipureintro; exact ⟨Hb, Hag⟩
  wp_apply wp_broadcast_chan_close dnc γ.done (rnDoneEsc γ (storage.walOf (GoInterface.ok si)))
    $$ [$Hbc]
  · imodintro; iunfold rnDoneEsc; iexact Hesc
  iintro -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
