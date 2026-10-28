/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Put.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Put
public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Proof.go_etcd_io.etcd.client.v3.KVMembers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Put` for any spec registered for `Put` (`kv.Put.specG`): `kv.Do` of `OpPut` at the spec,
the other two methods' specs unused (`doRunGen`'s put case). -/
theorem kv.Put.wp_generic
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.specG (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Put.specG (GF := GF) (hG := hG) := by
  intro api conn addr ci cd key val sl gs Sp Qp
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, #Hrpc, Hrun⟩
  obtain ⟨Hnp, Ht⟩ := Hnp
  wp_auto
  wp_apply wp_OpPut key val sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api conn addr ci cd opv (opPutModel key val gs) Sp Qp (fun _ _ _ => iprop(False))
      (fun _ => iprop(True)) (fun _ _ _ => iprop(False)) (fun _ => iprop(True)) $$ [Hrun]
    as %r %err Hout
  · iframe #
    unfold doRunGen
    iright
    ileft
    iframe # Hrun
    ipureintro; exact Ht
  ihave Hout' : putCallOut Qp r.put' err $$ [Hout]
  · have Heq : doOut (opPutModel key val gs) Qp (fun _ => iprop(True)) (fun _ => iprop(True)) r err =
        putCallOut Qp r.put' err := by
      unfold doOut; rw [Ht]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold putCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    unfold putCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    unfold putCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩


/-- `kv.Put` on a `*kv` of the members (`kv.Put.specM`, D44): `kv.Put.wp_generic` at the members'
plain spec at every metadata (`GrpcSpec.md (kvPutSpec ms)`), registered by `isKV`'s registrations
(`kvRegs_rpcPut`) and met by the caller's side (`putSpec_of`). -/
theorem kv.Put.wp_members
    (wp_Put : kv.Put.specG (GF := GF) (hG := hG)) :
    kv.Put.specM (GF := GF) (hG := hG) := by
  intro api ms ci cd key val sl gs Q F
  iintro %Φ ⟨#Pc, #Hkv, #Hctx, #Hce, #Hopts, %Hnp, #HF, Hrun⟩ HΦ
  obtain ⟨Hnp, Ht, Hl⟩ := Hnp
  iunfold isKV at Hkv
  icases Hkv with ⟨#Hobj, #Hregs⟩
  icases (kvObjAt_conn api (ms.map SrvAt.addr)).1 $$ Hobj with ⟨%conn, #Hobj⟩
  iapply (wp_Put api conn (ms.map SrvAt.addr) ci cd key val sl gs (GrpcSpec.md (kvPutSpec ms))
    (putAns ms F (putWireOf (opPutModel key val gs)) Q)) $$ [Hrun] HΦ
  iframe #
  isplitl []
  · ipureintro; exact ⟨Hnp, Ht⟩
  isplitl []
  · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcPut ms) $$ Hregs
  iapply (kvReqPre_wand api (ms.map SrvAt.addr) (floorsAt ms F) _ _
    ((putSpec_of ms F (putWireOf (opPutModel key val gs)) Q Hl).trans
      (attemptPre_md conn (GoInterface.ok ci) (kvPutSpec ms) _ _)))
  iframe HF Hrun

theorem kv.Put.wp_proof
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Put.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd key val sl gs Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, Hrun⟩
  obtain ⟨Hnp, Ht, Hl⟩ := Hnp
  wp_auto
  wp_apply wp_OpPut key val sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api γ dup ci cd opv (opPutModel key val gs) Q $$ [Hrun]
    as %r %err Hout
  · iframe #
    unfold doRunOk
    iright
    ileft
    iframe # Hrun
    ipureintro; exact ⟨Ht, Hl⟩
  ihave Hout' : putCallOut (putStOk (putWireOf (opPutModel key val gs)) Q) r.put' err $$ [Hout]
  · have Heq : doOut (opPutModel key val gs) (putStOk (putWireOf (opPutModel key val gs)) Q)
        (rangeStOk (rangeWireOf (opPutModel key val gs)) Q)
        (delStOk (deleteWireOf (opPutModel key val gs)) Q) r err =
        putCallOut (putStOk (putWireOf (opPutModel key val gs)) Q) r.put' err := by
      unfold doOut; rw [Ht]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold putCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    iapply putCallOut_st
    unfold putCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    iapply putCallOut_st
    unfold putCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
