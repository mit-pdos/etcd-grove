/-
`fieldpath.MakePathElementValueMap`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementValueMap
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

theorem fieldpath.MakePathElementValueMap.wp_proof
    (h_MakePathElementMap : fieldpath.MakePathElementMap.spec (GF := GF)) :
    fieldpath.MakePathElementValueMap.spec (GF := GF) := fun n => by
  wp_start as %Hn
  wp_auto
  wp_apply h_MakePathElementMap $$ [] as %v Hv
  · ipureintro; exact Hn
  iapply HΦ
  unfold ownPEVMapV
  iframe Hv
  ipureintro
  intro k x h; cases h

end proof

end smd
end EtcdGrove
end Perennial
