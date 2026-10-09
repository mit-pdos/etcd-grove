/-
Proof of `Spec/withTop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.withTop
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithSort
public import Spec.go_etcd_io.etcd.client.v3.WithLimit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem withTop.wp_proof (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithSort : WithSort.spec (GF := GF) (hG := hG))
    (wp_WithLimit : WithLimit.spec (GF := GF) (hG := hG)) :
    withTop.spec (GF := GF) (hG := hG) := by
  intro target order
  wp_start as %Hns
  iapply wp_fupd
  wp_auto
  wp_apply wp_WithPrefix as %f0 #H0
  wp_apply wp_WithSort target order as %f1 #H1
  · iframe #; ipureintro; exact Hns
  wp_apply wp_WithLimit as %f2 #H2
  wp_apply wp_slice_literal (l := [f0, f1, f2])
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  imodintro
  iapply HΦ
  unfold optsAt
  iexists [f0, f1, f2]
  iframe Hsl
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %f %g %Hf %Hg
  rcases i with _ | _ | _ | i
  · simp only [withTopM, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact H0
  · simp only [withTopM, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact H1
  · simp only [withTopM, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact H2
  · simp at Hf

end proof

end EtcdGrove
end Perennial
