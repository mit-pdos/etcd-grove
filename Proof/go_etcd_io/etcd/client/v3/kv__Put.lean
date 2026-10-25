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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem kv.Put.wp_members
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.specM (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Put.specM (GF := GF) (hG := hG) := by
  intro api ms ci cd key val sl gs Q F
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, #HF, Hrun⟩
  obtain ⟨Hnp, Ht, Hl⟩ := Hnp
  wp_auto
  wp_apply wp_OpPut key val sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api ms ci cd opv (opPutModel key val gs) (W64 0) F Q $$ [Hrun]
    as %r %err Hout
  · iframe #
    unfold doRunM
    iright
    ileft
    iframe # Hrun
    ipureintro; exact ⟨Ht, Hl⟩
  ihave Hout' : putCallOut (putAns ms F (putWireOf (opPutModel key val gs)) Q) r.put' err $$ [Hout]
  · have Heq : doOut (opPutModel key val gs) (putAns ms F (putWireOf (opPutModel key val gs)) Q)
        (rangeAns ms (W64 0) F (rangeWireOf (opPutModel key val gs)) Q)
        (delAns ms F (deleteWireOf (opPutModel key val gs)) Q) r err =
        putCallOut (putAns ms F (putWireOf (opPutModel key val gs)) Q) r.put' err := by
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


theorem kv.Put.wp_proof
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Put.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd key val sl gs Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, Hrun⟩
  obtain ⟨Hnp, Ht, Hl, Hw⟩ := Hnp
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
    ipureintro; exact ⟨Ht, Hl, Hw⟩
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
