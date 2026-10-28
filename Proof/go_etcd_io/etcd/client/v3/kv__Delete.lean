/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Delete.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Delete
public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
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

/-- `kv.Delete` for any spec registered for `DeleteRange` (`kv.Delete.specG`): `kv.Do` of
`OpDelete` at the spec, the other two methods' specs unused (`doRunGen`'s delete case). -/
theorem kv.Delete.wp_generic
    (wp_OpDelete : OpDelete.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.specG (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Delete.specG (GF := GF) (hG := hG) := by
  intro api conn addr ci cd key sl gs Sd Qd
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, #Hrpc, Hrun⟩
  obtain ⟨Hnp, Ht⟩ := Hnp
  wp_auto
  wp_apply wp_OpDelete key sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api conn addr ci cd opv (opDeleteModel key gs) (fun _ _ _ => iprop(False))
      (fun _ => iprop(True)) (fun _ _ _ => iprop(False)) (fun _ => iprop(True)) Sd Qd $$ [Hrun]
    as %r %err Hout
  · iframe #
    unfold doRunGen
    iright
    iright
    iframe # Hrun
    ipureintro; exact Ht
  ihave Hout' : deleteCallOut Qd r.del' err
      $$ [Hout]
  · have Heq : doOut (opDeleteModel key gs) (fun _ => iprop(True)) (fun _ => iprop(True)) Qd r err =
        deleteCallOut Qd r.del' err := by
      unfold doOut; rw [Ht]; simp only [show (W64 3 = W64 1) = False by decide,
        show (W64 3 = W64 2) = False by decide, ↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold deleteCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    unfold deleteCallOut
    ileft
    iframe Hm
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    unfold deleteCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩


/-- `kv.Delete` on a `*kv` of the members (`kv.Delete.specM`, D44): `kv.Delete.wp_generic` at the
members' plain spec at every metadata (`GrpcSpec.md (kvDeleteSpec ms)`; `kvRegs_rpcDelete`,
`deleteSpec_of`). -/
theorem kv.Delete.wp_members
    (wp_Delete : kv.Delete.specG (GF := GF) (hG := hG)) :
    kv.Delete.specM (GF := GF) (hG := hG) := by
  intro api ms ci cd key sl gs Q F
  iintro %Φ ⟨#Pc, #Hkv, #Hctx, #Hce, #Hopts, %Hnp, #HF, Hrun⟩ HΦ
  obtain ⟨Hnp, Ht, Hz⟩ := Hnp
  iunfold isKV at Hkv
  icases Hkv with ⟨#Hobj, #Hregs⟩
  icases (kvObjAt_conn api (ms.map SrvAt.addr)).1 $$ Hobj with ⟨%conn, #Hobj⟩
  iapply (wp_Delete api conn (ms.map SrvAt.addr) ci cd key sl gs (GrpcSpec.md (kvDeleteSpec ms))
    (delAns ms F (deleteWireOf (opDeleteModel key gs)) Q)) $$ [Hrun] HΦ
  iframe #
  isplitl []
  · ipureintro; exact ⟨Hnp, Ht⟩
  isplitl []
  · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcDelete ms) $$ Hregs
  iapply (kvReqPre_wand api (ms.map SrvAt.addr) (floorsAt ms F) _ _
    ((deleteSpec_of ms F (deleteWireOf (opDeleteModel key gs)) Q Hz).trans
      (attemptPre_md conn (GoInterface.ok ci) (kvDeleteSpec ms) _ _)))
  iframe HF Hrun

theorem kv.Delete.wp_proof
    (wp_OpDelete : OpDelete.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Delete.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd key sl gs Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, Hrun⟩
  obtain ⟨Hnp, Ht, Hz⟩ := Hnp
  wp_auto
  wp_apply wp_OpDelete key sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api γ dup ci cd opv (opDeleteModel key gs) Q $$ [Hrun]
    as %r %err Hout
  · iframe #
    unfold doRunOk
    iright
    iright
    iframe # Hrun
    ipureintro; exact ⟨Ht, Hz⟩
  ihave Hout' : deleteCallOut (delStOk (deleteWireOf (opDeleteModel key gs)) Q) r.del' err
      $$ [Hout]
  · have Heq : doOut (opDeleteModel key gs) (putStOk (putWireOf (opDeleteModel key gs)) Q)
        (rangeStOk (rangeWireOf (opDeleteModel key gs)) Q)
        (delStOk (deleteWireOf (opDeleteModel key gs)) Q) r err =
        deleteCallOut (delStOk (deleteWireOf (opDeleteModel key gs)) Q) r.del' err := by
      unfold doOut; rw [Ht]; simp only [show (W64 3 = W64 1) = False by decide,
        show (W64 3 = W64 2) = False by decide, ↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold deleteCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    iapply deleteCallOut_st
    unfold deleteCallOut
    ileft
    iframe Hm
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    iapply deleteCallOut_st
    unfold deleteCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
