/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Put.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Put
public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.ContextError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem kv.Put.wp_proof
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Put.spec (GF := GF) (hG := hG) := by
  intro api addr ci cd key val sl gs Spec Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, #Hek, %Hnp, #Hrpc, #Hrun⟩
  obtain ⟨Hnp, Ht⟩ := Hnp
  wp_auto
  wp_apply wp_OpPut key val sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api addr ci cd opv (opPutModel key val gs) Spec Q (fun _ _ => iprop(True))
    (fun _ => iprop(True)) (fun _ _ => iprop(True)) (fun _ => iprop(True)) $$ []
    as %r %err ⟨Hout, -⟩
  · iframe #
    unfold doRunOk
    iright
    ileft
    iframe #
    ipureintro; exact Ht
  ihave Hout' : putCallOut Q r.put' err $$ [Hout]
  · have Heq : doOut (opPutModel key val gs) Q (fun _ => iprop(True)) (fun _ => iprop(True)) r err =
        putCallOut Q r.put' err := by
      unfold doOut; rw [Ht]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold putCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse⟩)
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
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse'⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    iapply HΦ
    unfold putCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
