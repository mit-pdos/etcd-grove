/-
Proof of `Spec/Cache__serverRevision.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__serverRevision
public import Spec.go_etcd_io.etcd.client.v3.WithLimit
public import Spec.go_etcd_io.etcd.client.v3.WithCountOnly

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.serverRevision.wp_proof
    (wp_WithLimit : WithLimit.spec (GF := GF) (hG := hG))
    (wp_WithCountOnly : WithCountOnly.spec (GF := GF) (hG := hG)) :
    Cache.serverRevision.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap ctx s
  wp_start as ⟨#Hc, #Hctx⟩
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  unfold isCacheFields
  iNamed Hc
  wp_auto
  wp_join iprop(key_ptr ↦ (if cf.pfx = [] then (go!"/" : GoString) else cf.pfx)) with [key]
    as key
  · rw [ite_eq_left Hif]; iframe
  · rw [ite_eq_right Hif]; iframe
  wp_apply wp_WithLimit (W64 1) as %f1 #Hf1
  wp_apply wp_WithCountOnly as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  generalize hsl : slice.mk sl _ _ = optsSl
  have hfs : [f1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2 = [f1, f2] := by
    show [f1, zero_val GoFunc].set 1 f2 = [f1, f2]; rfl
  ihave #Hopts : optsAt optsSl ([withLimitM (W64 1), withCountOnlyM] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · simp at Hf
  iunfold isEtcdKV at HisKV
  ihave #HG := HisKV $$ %ctx %s %(if cf.pfx = [] then (go!"/" : GoString) else cf.pfx) %optsSl
    %([withLimitM (W64 1), withCountOnlyM] : List (OpFull → OpFull)) %(W64 0)
  wp_apply HG $$ [] as %resp %err #Hres
  · iframe Hctx Hopts
    isplitr
    · iapply etcdReached_zero
    ipureintro
    refine ⟨?_, rfl⟩
    rintro ⟨h, -⟩
    cases h
  iunfold kvGetResult at Hres
  icases Hres with (%Herr | ⟨%Herr, %r, %m, #Hrev, #Hm, -, -, -⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact ⟨Herr, rfl⟩
  · subst Herr
    iunfold getRespRev at Hrev
    icases Hrev with ⟨%hdr, #Hh, %Hnn, #Hr⟩
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists m
    iexact Hm

end proof

end EtcdGrove
end Perennial
