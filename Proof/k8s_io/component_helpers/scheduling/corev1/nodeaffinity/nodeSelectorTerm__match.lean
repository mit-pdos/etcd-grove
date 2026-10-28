/-
Proof of `Spec/k8s_io/component_helpers/scheduling/corev1/nodeaffinity/nodeSelectorTerm__match.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.nodeSelectorTerm__match

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.component_helpers.scheduling.corev1.nodeaffinity

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

theorem nodeSelectorTerm.match.wp_proof : nodeSelectorTerm.match.spec (GF := GF) (hG := hG) := by
  intro t tv lm dql oL fm dqf oF
  wp_start as ⟨Ht, #Hok, HL, HF⟩
  iunfold termOk at Hok
  icases Hok with ⟨#HmL, #HmF, %es, #Hes⟩
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ
    iframe
    ipureintro; exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h Hif⟩
  have Hpe := Hif
  iunfold optMatcherOk at HmL
  icases HmL with (%HLn | #HmL)
  · rw [HLn]
    wp_auto
    iunfold optMatcherOk at HmF
    icases HmF with (%HFn | #HmF)
    · rw [HFn]
      wp_auto
      iapply HΦ
      iframe
      ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
    · iunfold matcherOk at HmF
      icases HmF with ⟨%j, %Hj, #HmF⟩
      rw [Hj]
      wp_auto
      wp_apply (wp_ownMapD_len (t := k8s_io.apimachinery.pkg.fields.Set'.ty) fm dqf oF) $$ [$HF]
        as %n HF
      wp_if_destruct
      · rw [Hj]
        wp_apply HmF $$ %fm %dqf %oF [$HF] as %b HF
        cases b
        · wp_auto
          iapply HΦ
          iframe
          ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
        · wp_auto
          iapply HΦ
          iframe
          ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
      · iapply HΦ
        iframe
        ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
  · iunfold matcherOk at HmL
    icases HmL with ⟨%i, %Hi, #HmL⟩
    rw [Hi]
    wp_auto
    rw [Hi]
    wp_apply HmL $$ %lm %dql %oL [$HL] as %bl HL
    cases bl
    · wp_auto
      iapply HΦ
      iframe
      ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
    wp_auto
    iunfold optMatcherOk at HmF
    icases HmF with (%HFn | #HmF)
    · rw [HFn]
      wp_auto
      iapply HΦ
      iframe
      ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
    · iunfold matcherOk at HmF
      icases HmF with ⟨%j, %Hj, #HmF⟩
      rw [Hj]
      wp_auto
      wp_apply (wp_ownMapD_len (t := k8s_io.apimachinery.pkg.fields.Set'.ty) fm dqf oF) $$ [$HF]
        as %n HF
      wp_if_destruct
      · rw [Hj]
        wp_apply HmF $$ %fm %dqf %oF [$HF] as %b HF
        cases b
        · wp_auto
          iapply HΦ
          iframe
          ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
        · wp_auto
          iapply HΦ
          iframe
          ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩
      · iapply HΦ
        iframe
        ipureintro; exact ⟨fun h => absurd Hpe h, fun _ => rfl⟩

end proof

end dsctl
end EtcdGrove
end Perennial
