/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__onStop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__onStop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrashSteps

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
  intro E γ r
  wp_start as ⟨#Hr, Hdone, HST, Hrun, Hwt, Hwst, Hwap, ⟨%S, %p, %L, %sent, Hwvo, Hprod, #Hidx, %Ha0, #HcL⟩,
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
  iunfold rnDoneTok at Hdone
  icases Hdone with ⟨%dnc', %st2, #Hdnc', #Hst2, Hbc⟩
  icombine Hdnc Hdnc' gives %Heq
  subst Heq
  icombine Hst Hst2 gives %Hsteq3
  have Hsteq3' : stm = st2 := by first | exact Hsteq3 | exact Hsteq3.2
  subst Hsteq3'
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto_lc 1
  -- (R2b-1 stage 6) the records, taken out of the durability invariant; (P5) with raft's durable
  -- state, at the generation not crashed (`rnDurK_take.law`)
  iunfold rnWalView at Hwvo
  iapply (wp_ncfupd _ _ (by rfl))
  unfold ncfupd
  iintro Hnc
  imod rnDurK_take_law_holds γ.node γ.id γ.walK γ.wal.h _ rfl $$ Hdur Hnc Hlc1 Hwst Hwap Hwvo
    with ⟨Hnc, -, HrS, %σ, Hrecs, %Hσ, #Hσc⟩
  imodintro
  iframe Hnc
  rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Stop")]
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Stop")]
  wp_auto
  wp_apply HStop $$ [$Hrun] as ⟨-, Hvac⟩
  wp_apply HtkStop
  wp_apply HTrStop $$ [$HST]
  ihave #HClose := walClose_spec stm γ.wal.h γ.ss si Hsieq σ γ.id cid true $$ Hsti
  subst Hsieq
  wp_apply HClose $$ [$Hwo $Hrecs $Hmeta $Hpurge] as %cerr ⟨%hcerr, Hfiles⟩
  · ipureintro; omega
  subst hcerr
  (try wp_auto)
  -- (R2b-3b) the stop's escrow, with the image: the id vacant, the durable state, the files
  imod inv_alloc rnStopN ⊤ iprop(rnStopImage γ ∨ token γ.sc)
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
  wp_apply wp_broadcast_chan_close dnc γ.done (rnDoneEsc γ)
    $$ [$Hbc]
  · imodintro; iunfold rnDoneEsc; iexact Hesc
  iintro -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
