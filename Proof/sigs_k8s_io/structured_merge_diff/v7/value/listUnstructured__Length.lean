/-
`value.listUnstructured.Length`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
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

theorem value.listUnstructured.Length.wp_proof :
    value.listUnstructured.Length.spec (GF := GF) := fun l vs => by
  wp_start as Hl
  icases isListV_val $$ Hl with ⟨%xs, #Hs, HL⟩
  ihave %Hlen := isIfaceL_length $$ HL
  ihave %Hsl := ownSlice_len $$ Hs
  wp_auto
  wp_end
  ipureintro
  word

end proof

end smd
end EtcdGrove
end Perennial
