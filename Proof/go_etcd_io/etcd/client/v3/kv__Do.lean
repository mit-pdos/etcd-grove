/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Do.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.Op__IsSortOptionValid
public import Spec.go_etcd_io.etcd.client.v3.Op__toRangeRequest
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Range
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Put
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

theorem kv.Do.wp_proof
    (wp_IsSortOptionValid : Op.IsSortOptionValid.spec (GF := GF) (hG := hG))
    (wp_toRangeRequest : Op.toRangeRequest.spec (GF := GF) (hG := hG))
    (wp_retry_Range : retryKVClient.Range.spec (GF := GF) (hG := hG))
    (wp_retry_Put : retryKVClient.Put.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Do.spec (GF := GF) (hG := hG) := by
  intro api K ci cd opv o Qp Qr
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hat, Hrun⟩
  iunfold kvObjAt at Hkv
  icases Hkv with ⟨%rkv, %conn, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok⟩
  ihave Hat' := Hat
  iunfold opFullAt at Hat'
  icases Hat' with ⟨-, -, %Hf2, -, -⟩
  obtain ⟨ht, -⟩ := Hf2
  wp_auto
  rw [ht]
  iunfold doRunOk at Hrun
  icases Hrun with (⟨%Hr, #Hrun⟩ | ⟨%Hp, #Hrun⟩)
  · -- a range
    obtain ⟨Ht, Hs⟩ := Hr
    rw [Ht]
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_IsSortOptionValid opv o $$ []
    · iframe #; ipureintro; exact Hs
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_toRangeRequest opv o $$ [] as %r ⟨%req, Hr, #Hk, #He, %Hreq⟩
    · iframe #; ipureintro; exact ⟨Ht, Hs⟩
    ihave #Hrun' : rangeRunOk K (rangeReqOp req o.key o.base.rangeEnd) Qr $$ []
    · rw [Hreq]; iexact Hrun
    wp_apply wp_retry_Range rkv conn K ci cd r req o.key o.base.rangeEnd sl vs Qr $$ [Hr]
      as %resp %err ⟨-, #Hres⟩
    · iframe #
      iframe
      ipureintro; exact Hcap
    iunfold rangeCallOut at Hres
    icases Hres with (⟨%Herr, #Hm⟩ | %Herr)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      simp only [Ht, ↓reduceIte]
      unfold rangeCallOut
      ileft
      iframe #
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) as %err' %Herr'
        · iframe #; ipureintro; exact fun _ => Hce'
        iapply HΦ
        unfold doOut
        simp only [Ht, ↓reduceIte]
        unfold rangeCallOut
        iright
        ipureintro
        exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩
  · -- a put
    rw [Hp]
    wp_auto
    ihave Hat' := Hat
    iunfold opFullAt at Hat'
    icases Hat' with ⟨Hat0, #Hkey, %Hf2, #Hval, -⟩
    iunfold opAt at Hat0
    icases Hat0 with ⟨%Hf, -⟩
    unfold OpFields at Hf
    obtain ⟨-, hpk, -⟩ := Hf
    obtain ⟨-, -, -, -, hlease, hiv, hil, -⟩ := Hf2
    ihave #Hrun' : putRunOk K (putReqOp
        { state' := zeroValDef, Key' := opv.key', Value' := opv.val', Lease' := opv.leaseID',
          PrevKv' := opv.prevKV', IgnoreValue' := opv.ignoreValue',
          IgnoreLease' := opv.ignoreLease', unknownFields' := slice.nil, sizeCache' := 0 }
        o.key o.val) Qp $$ []
    · simp only [putReqOp, putWireOf, hlease, hpk, hiv, hil]
      iexact Hrun
    wp_apply wp_retry_Put rkv conn K ci cd _ _ o.key o.val sl vs Qp $$ [«$r0»]
      as %resp %err ⟨-, #Hres⟩
    · iframe #
      iframe
    iunfold putCallOut at Hres
    icases Hres with (⟨%Herr, #Hm⟩ | %Herr)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      rw [Hp]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
      unfold putCallOut
      ileft
      iframe #
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) as %err' %Herr'
        · iframe #; ipureintro; exact fun _ => Hce'
        iapply HΦ
        unfold doOut
        rw [Hp]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
        unfold putCallOut
        iright
        ipureintro
        exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

end proof

end EtcdGrove
end Perennial
