/-
Proof of `Spec/k8s_io/component_helpers/scheduling/corev1/nodeaffinity/extractNodeFields.lean`,
over gap D2's body hypothesis. Lean-first.
-/
module

public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.extractNodeFields
public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.extractNodeFields_body

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

theorem extractNodeFields.wp_proof (h_body : extractNodeFields_body.spec (sem := sem)) :
    extractNodeFields.spec (GF := GF) (hG := hG) := by
  haveI := h_body
  intro n dq v d
  wp_start as ⟨Hl, Hd⟩
  icases node_name_eq v dq d $$ Hd with ⟨Hd, %Hname⟩
  wp_auto
  rw [go.make1_underlying, (go.is_underlying :
    underlying k8s_io.apimachinery.pkg.fields.Set'.ty = _)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %m Hm
  icases (Access.access
      (A := n.[k8s_io.api.core.v1.Node, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta,
        go!"Name"] ↦{dq} v.ObjectMeta'.Name')
      (A' := n.[k8s_io.api.core.v1.Node, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta,
        go!"Name"] ↦{dq} v.ObjectMeta'.Name')
      (P := n ↦{dq} v)) $$ Hl with ⟨Hf, Hl⟩
  wp_auto
  wp_func_call
  wp_call
  by_cases hl : v.ObjectMeta'.Name'.length < 2 ^ 63
  case neg => simp only [hl, ↓reduceIte]; wp_apply wp_AngelicExit
  simp only [hl, ↓reduceIte]
  wp_auto
  have hz : sint.Z (W64 (v.ObjectMeta'.Name'.length : Int)) = v.ObjectMeta'.Name'.length := by word
  wp_if_destruct
  · have hne : v.ObjectMeta'.Name' ≠ [] := by
      intro h; rw [hz, h] at Hif; simp at Hif
    wp_apply (wp_mapInsert go.string m ∅ go!"metadata.name" v.ObjectMeta'.Name') $$ [$Hm] as Hm
    ihave Hl := Hl $$ Hf
    iapply HΦ
    unfold nodeFieldsM
    rw [← Hname]; simp only [hne, ↓reduceIte, GMap.insert_empty]
    iframe
  · have he : v.ObjectMeta'.Name' = [] := by
      have h1 : ¬ (0 : Int) < v.ObjectMeta'.Name'.length := by
        rw [← hz]; simpa [show sint.Z (W64 0) = 0 from rfl] using Hif
      exact List.eq_nil_of_length_eq_zero (by omega)
    ihave Hl := Hl $$ Hf
    iapply HΦ
    unfold nodeFieldsM
    rw [← Hname]; simp only [he, ↓reduceIte]
    iframe

end proof

end dsctl
end EtcdGrove
end Perennial
