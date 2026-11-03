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
  wp_start as ⟨#Hr, Hdone, HST, Hrun, Hwt, Hwst, Hwap, ⟨%v, Hwvo, %Hvp⟩, ⟨%stm, %id, %cid, #Hstm, Hmeta, Hpurge⟩⟩
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
  imod rnDur_take γ.wal (storage.walOf stm) v Hvp $$ Hdur Hwst Hwap Hwv Hwok
    with ⟨%σ, Hrecs, %Hσ⟩
  obtain ⟨-, Hσb, Hσc⟩ := Hσ
  iunfold rnDoneTok at Hdone
  icases Hdone with ⟨%dnc', #Hdnc', Hbc⟩
  icombine Hdnc Hdnc' gives %Heq
  subst Heq
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Stop")]
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Stop")]
  wp_auto
  wp_apply HStop $$ [$Hrun] as -
  wp_apply HtkStop
  wp_apply HTrStop $$ [$HST]
  ihave #HClose := walClose_spec stm si Hsieq σ id cid $$ Hsti
  subst Hsieq
  wp_apply HClose $$ [$Hwo $Hrecs $Hmeta $Hpurge] as %cerr Hcerr
  · ipureintro; omega
  icases Hcerr with (⟨%hcerr, -⟩ | %Hcerr)
  rotate_left
  · exact absurd Hwco Hcerr
  subst hcerr
  (try wp_auto)
  wp_apply wp_broadcast_chan_close dnc γ.done iprop(True) $$ [$Hbc]
  · imodintro; itrivial
  iintro -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
