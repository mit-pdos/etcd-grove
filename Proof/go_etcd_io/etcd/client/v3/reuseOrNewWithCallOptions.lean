/-
Proof of `Spec/go_etcd_io/etcd/client/v3/reuseOrNewWithCallOptions.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.reuseOrNewWithCallOptions

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem reuseOrNewWithCallOptions.wp_proof :
    reuseOrNewWithCallOptions.spec (GF := GF) (hG := hG) := by
  intro o sl ros
  wp_start as ⟨#Ho, #Hsl, #Hros⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_auto
  wp_if_destruct
  · iapply HΦ; iexact Ho
  iunfold retryOptsAt at Ho
  icases Ho with ⟨%ov, #Hov, #Hok⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (fv : go_etcd_io.etcd.client.v3.retryOption)
      (cv : go_etcd_io.etcd.client.v3.options),
      "i" ∷ i_ptr ↦ n ∗ "f" ∷ f_ptr ↦ fv ∗ "cp" ∷ «$r0_ptr» ↦ cv ∗ "#Hcv" ∷ optionsOk cv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ros.length : Int)⌝) $$ [i f «$r0»]
  · iexists W64 0, _, ov
    simp only [named]
    iframe
    iframe #
    ipureintro; constructor <;> word
  wp_for IH
  by_cases Hlt' : sint.Z n < sint.Z sl.len
  rotate_left
  · simp only [decide_eq_false Hlt', Bool.false_eq_true, ↓reduceIte]
    ipersist cp
    wp_auto
    iapply HΦ
    unfold retryOptsAt
    iexists cv
    iframe #
  wp_if_destruct
  rotate_left
  · exact absurd Hlt' Hif
  · have Hlt : sint.nat n < ros.length := by word
    obtain ⟨ro, Hro⟩ : ∃ ro, ros[sint.nat n]? = some ro := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) ro sl DFrac.discard ros Hn.1 Hro $$ Hsl with ⟨#Hre, -⟩
    ihave #Happ := BigSepL.bigSepL_lookup (Φ := fun _ (r : go_etcd_io.etcd.client.v3.retryOption) =>
      optApplyOk (GF := GF) r.applyFunc') Hro $$ Hros
    wp_auto
    iunfold optApplyOk at Happ
    wp_apply Happ $$ %«$r0_ptr» %cv [cp] as Hcp
    · iframe #; iframe
    icases Hcp with ⟨%cv', Hcp, #Hcv'⟩
    wp_for_post
    iframe
    iexists n + W64 1, ro, cv'
    simp only [named]
    iframe
    iframe #
    ipureintro; constructor <;> word

end proof

end EtcdGrove
end Perennial
