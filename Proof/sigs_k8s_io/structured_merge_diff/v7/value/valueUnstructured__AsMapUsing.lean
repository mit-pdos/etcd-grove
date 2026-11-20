/-
`value.valueUnstructured.AsMapUsing`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.valueUnstructured.AsMapUsing.wp_proof :
    value.valueUnstructured.AsMapUsing.spec (GF := GF) := fun ⟨i⟩ kvs al => by
  wp_start as #Hi
  ihave %Hsh := isIface_map_shape $$ Hi
  obtain ⟨gm, rfl⟩ := Hsh
  wp_auto
  iapply HΦ
  iapply isMapV_intro
  iexact Hi

end proof

end smd
end EtcdGrove
end Perennial
