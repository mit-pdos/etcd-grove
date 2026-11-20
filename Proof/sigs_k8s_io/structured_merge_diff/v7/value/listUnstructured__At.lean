/-
`value.listUnstructured.At`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
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

theorem value.listUnstructured.At.wp_proof
    (h_NewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    value.listUnstructured.At.spec (GF := GF) := fun l vs n x => by
  wp_start as ⟨Hl, %Hx⟩
  icases isListV_val $$ Hl with ⟨%xs, #Hs, HL⟩
  ihave ⟨%i, %Hxi, Hi⟩ := isIfaceL_lookup xs vs _ x Hx.2 $$ HL
  ihave %Hsl := ownSlice_len $$ Hs
  have hlt : (BitVec.toInt n).toNat < xs.length := (List.getElem?_eq_some_iff.mp Hxi).1
  have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z l.len := by constructor <;> word
  wp_auto
  simp only [hb, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index l (sint.Z n) xs DFrac.discard i (by word) as -
  · isplitr
    · iexact Hs
    · ipureintro; exact Hxi
  wp_apply h_NewValueInterface i x $$ [Hi] as %v Hv
  · iexact Hi
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
