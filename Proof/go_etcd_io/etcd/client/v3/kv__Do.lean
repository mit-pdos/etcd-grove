/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Do.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.Op__IsSortOptionValid
public import Spec.go_etcd_io.etcd.client.v3.Op__toRangeRequest
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Range
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Put
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__DeleteRange
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
    (wp_retry_DeleteRange : retryKVClient.DeleteRange.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Do.spec (GF := GF) (hG := hG) := by
  intro api addr ci cd opv o Sp Qp Sr Qr Sd Qd
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hat, Hrun⟩
  iunfold kvObjAt at Hkv
  icases Hkv with ⟨%rkv, %conn, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, %Hsc⟩
  ihave Hat' := Hat
  iunfold opFullAt at Hat'
  icases Hat' with ⟨-, -, %Hf2, -, -⟩
  obtain ⟨ht, -⟩ := Hf2
  wp_auto
  rw [ht]
  iunfold doRunOk at Hrun
  icases Hrun with (⟨%Ht, #Hsn, #Hrpc, #Hrun⟩ | ⟨%Hp, #Hrpc, Hrun⟩ | ⟨%Hd, #Hrpc, Hrun⟩)
  · -- a range
    rw [Ht]
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_IsSortOptionValid opv o $$ []
    · iframe #
    cases hsv : sortValid o
    · -- an invalid sort option: `rpctypes.ErrInvalidSortOption`
      have hss : o.base.sortSet = true := by
        cases h : o.base.sortSet
        · simp [sortValid, h] at hsv
        · rfl
      simp only [sortNamesIf, hss, ↓reduceIte]
      ihave #Hsn' := Hsn
      iunfold sortNamesOk at Hsn'
      icases Hsn' with ⟨⟨%e, #He, %Hev, #Hse, #Hcl⟩, -, -⟩
      wp_auto
      wp_apply wp_ContextError ci cd e $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
      · iframe #; ipureintro; exact fun _ => Hev.2
      ihave #Hcl' := Hclw $$ Hcl
      iapply HΦ
      unfold doOut
      simp only [Ht, ↓reduceIte]
      unfold rangeCallOut
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 Hev.1).1, (Herr'.2 Hev.1).2, rfl⟩
    wp_auto
    try wp_method_call
    try wp_call
    wp_auto
    wp_apply wp_toRangeRequest opv o $$ [] as %r ⟨%req, Hr, #Hk, #He, %Hreq⟩
    · iframe #; ipureintro; exact Ht
    ihave #Hrun' : □ ▷ Sr (rangeReqOp req o.key o.base.rangeEnd) Qr $$ []
    · rw [Hreq]; iexact Hrun
    wp_apply wp_retry_Range rkv conn addr Sr Qr ci cd r req o.key o.base.rangeEnd sl vs $$ [Hr]
      as %resp %err ⟨-, Hres⟩
    · iframe #
      iframe
      ipureintro; exact Hcap
    iunfold rangeCallOut at Hres
    icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      simp only [Ht, ↓reduceIte]
      unfold rangeCallOut
      ileft
      iframe Hm
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
        · iframe #; ipureintro; exact fun _ => Hce'
        ihave #Hcl' := Hclw $$ Hcl
        iapply HΦ
        unfold doOut
        simp only [Ht, ↓reduceIte]
        unfold rangeCallOut
        iright
        iframe #
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
    ihave Hrun' : reqPre conn addr vs (Sp (putReqOp
        { state' := zeroValDef, Key' := opv.key', Value' := opv.val', Lease' := opv.leaseID',
          PrevKv' := opv.prevKV', IgnoreValue' := opv.ignoreValue',
          IgnoreLease' := opv.ignoreLease', unknownFields' := slice.nil, sizeCache' := 0 }
        o.key o.val) Qp) $$ [Hrun]
    · simp only [putReqOp, putWireOf, hlease, hpk, hiv, hil]
      iapply kvReqPre_conn api rkv conn addr vs _ Hsc $$ [Hrun]
      iframe Hremote Hrkv Hrun
    wp_apply wp_retry_Put rkv conn addr Sp Qp ci cd _ _ o.key o.val sl vs $$ [«$r0» Hrun']
      as %resp %err ⟨-, Hres⟩
    · iframe #
      iframe
      try (simp only []; iframe #)
    iunfold putCallOut at Hres
    icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      rw [Hp]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
      unfold putCallOut
      ileft
      iframe Hm
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
        · iframe #; ipureintro; exact fun _ => Hce'
        ihave #Hcl' := Hclw $$ Hcl
        iapply HΦ
        unfold doOut
        rw [Hp]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
        unfold putCallOut
        iright
        iframe #
        ipureintro
        exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

  · -- a delete
    rw [Hd]
    wp_auto
    ihave Hat' := Hat
    iunfold opFullAt at Hat'
    icases Hat' with ⟨Hat0, #Hkey, -, -, -⟩
    iunfold opAt at Hat0
    icases Hat0 with ⟨%Hf, #Hend⟩
    unfold OpFields at Hf
    obtain ⟨-, hpk, -⟩ := Hf
    ihave Hrun' : reqPre conn addr vs (Sd (deleteReqOp
        { state' := zeroValDef, Key' := opv.key', RangeEnd' := opv.end', PrevKv' := opv.prevKV',
          unknownFields' := slice.nil, sizeCache' := 0 }
        o.key o.base.rangeEnd) Qd) $$ [Hrun]
    · simp only [deleteReqOp, deleteWireOf, hpk]
      iapply kvReqPre_conn api rkv conn addr vs _ Hsc $$ [Hrun]
      iframe Hremote Hrkv Hrun
    wp_apply wp_retry_DeleteRange rkv conn addr Sd Qd ci cd _ _ o.key o.base.rangeEnd sl vs
      $$ [«$r0» Hrun'] as %resp %err ⟨-, Hres⟩
    · iframe #
      iframe
      try (simp only []; iframe #)
    iunfold deleteCallOut at Hres
    icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      rw [Hd]; simp only [show (W64 3 = W64 1) = False by decide,
        show (W64 3 = W64 2) = False by decide, ↓reduceIte]
      unfold deleteCallOut
      ileft
      iframe Hm
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
        · iframe #; ipureintro; exact fun _ => Hce'
        ihave #Hcl' := Hclw $$ Hcl
        iapply HΦ
        unfold doOut
        rw [Hd]; simp only [show (W64 3 = W64 1) = False by decide,
          show (W64 3 = W64 2) = False by decide, ↓reduceIte]
        unfold deleteCallOut
        iright
        iframe #
        ipureintro
        exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

end proof

end EtcdGrove
end Perennial
