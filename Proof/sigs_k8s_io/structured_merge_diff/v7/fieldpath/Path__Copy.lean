/-
`fieldpath.Path.Copy`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Path__Copy
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

theorem fieldpath.Path.Copy.wp_proof :
    fieldpath.Path.Copy.spec (GF := GF) := fun s dq p => by
  wp_start as Hp
  unfold isPathF
  icases Hp with ⟨%es, Hs, #Hp⟩
  ihave %hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply (wp_slice_make2 (V := fieldpath.PathElement) s.len) as %sl ⟨Hsl, -⟩
  · ipureintro; exact hl.2
  wp_apply (wp_slice_copy sl _ s es dq) $$ [$Hsl $Hs] as %n ⟨-, Hsl, Hs⟩
  have e : List.take (List.replicate (sint.nat s.len) (zero_val fieldpath.PathElement)).length es ++
      List.drop es.length (List.replicate (sint.nat s.len) (zero_val fieldpath.PathElement)) = es := by
    rw [List.length_replicate, show sint.nat s.len = es.length by omega, List.take_length]
    simp
  rw [e]
  iapply HΦ
  isplitl [Hs]
  · iexists es; iframe; iexact Hp
  · iexists es; iframe; iexact Hp

end proof

end smd
end EtcdGrove
end Perennial
