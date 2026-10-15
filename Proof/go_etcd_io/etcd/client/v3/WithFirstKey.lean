/-
Proof of `Spec/go_etcd_io/etcd/client/v3/WithFirstKey.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithFirstKey
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithLimit
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

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

theorem WithFirstKey.wp_proof (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithLimit : WithLimit.spec (GF := GF) (hG := hG)) :
    WithFirstKey.spec (GF := GF) (hG := hG) := by
  wp_start
  iapply wp_fupd
  (try wp_auto)
  wp_func_call
  wp_call
  simp only [go_etcd_io.etcd.client.v3.SortAscend, go_etcd_io.etcd.client.v3.SortByKey]
  (try wp_auto)
  wp_apply wp_WithPrefix as %f0 #H0
  (try wp_auto)
  wp_func_call
  wp_call
  (try wp_auto)
  ipersist target
  wp_apply wp_WithLimit as %f2 #H2
  simp only [recv_eq_func_mk]
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  ipersist Hsl
  (try wp_auto)
  imodintro
  iapply HΦ
  isplitl [order]
  · iexists iprop(∃ v : w64, order_ptr ↦ v ∗ ⌜v = W64 1 ∨ v = W64 0⌝)
    isplitl [order]
    · iexists W64 1
      iframe order
      ipureintro; left; rfl
    unfold optsAtRes
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
      List.set_cons_succ, List.set_cons_zero] at Hf
    rcases i with _ | _ | _ | i
    · simp only [withTopM, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg
      subst Hf Hg
      iapply optSpec_res $$ H0
    · simp only [withTopM, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg
      subst Hf Hg
      unfold optSpecRes
      imodintro
      iintro %opp %op %o
      wp_start as ⟨⟨%v, Hord, %Hv⟩, Hop, #Hat⟩
      iapply wp_fupd
      simp only [go_etcd_io.etcd.client.v3.SortAscend, go_etcd_io.etcd.client.v3.SortByKey,
        go_etcd_io.etcd.client.v3.SortNone]
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
        ipersist «$r0»
        imodintro
        iapply HΦ
        iframe Hop
        isplitl [Hord]
        · iexists W64 0
          iframe Hord
          ipureintro; right; rfl
        unfold opFullAt opAt OpFields
        icases Hat with ⟨⟨%Hf, #He⟩, #Hk, %Ht, #Hv, #Hs⟩
        simp only [withSortM]
        iframe #
        isplitl []
        · ipureintro; simp_all
        isplitl []
        · ipureintro; simp_all
        unfold opSortAt
        simp only [↓reduceIte, and_self]
        iexact «$r0»
      · have hv0 : v = W64 0 := by rcases Hv with h | h <;> simp_all
        subst hv0
        (try wp_auto)
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
        ipersist «$r0»
        imodintro
        iapply HΦ
        iframe Hop
        isplitl [Hord]
        · iexists W64 0
          iframe Hord
          ipureintro; right; rfl
        unfold opFullAt opAt OpFields
        icases Hat with ⟨⟨%Hf, #He⟩, #Hk, %Ht, #Hv, #Hs⟩
        simp only [withSortM]
        iframe #
        isplitl []
        · ipureintro; simp_all
        isplitl []
        · ipureintro; simp_all
        unfold opSortAt
        simp only [↓reduceIte, and_self]
        iexact «$r0»
    · simp only [withTopM, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf Hg
      subst Hf Hg
      iapply optSpec_res $$ H2
    · simp at Hf
  iexact Hcap

end proof

end EtcdGrove
end Perennial
