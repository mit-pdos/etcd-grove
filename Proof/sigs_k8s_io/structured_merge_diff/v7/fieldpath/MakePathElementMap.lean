/-
`fieldpath.MakePathElementMap`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementMap
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.MakePathElementMap.wp_proof :
    fieldpath.MakePathElementMap.spec (GF := GF) := fun n => by
  wp_start as %Hn
  wp_auto
  wp_apply (wp_slice_make3 (V := fieldpath.pathElementValue) (W64 0) n (by word)) as %sl ⟨Hsl, Hcap, %Hc⟩
  iapply HΦ
  unfold ownPEMapV
  iexists [], []
  simp only [List.replicate, List.map_nil]
  iframe Hsl Hcap
  unfold isPEL
  isplit
  · itrivial
  · ipureintro; exact ⟨trivial, List.Pairwise.nil, fun _ => rfl⟩

end proof

end smd
end EtcdGrove
end Perennial
