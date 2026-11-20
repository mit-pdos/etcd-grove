/-
`value.mapUnstructuredString.Has`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Has
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

theorem value.mapUnstructuredString.Has.wp_proof :
    value.mapUnstructuredString.Has.spec (GF := GF) := fun m kvs k => by
  wp_start as Hm
  ihave Hi := isMapV_val $$ Hm
  icases isIface_map_val $$ Hi with ⟨%M, #HM, %Hk, -⟩
  wp_auto
  wp_apply wp_map_lookup2 go.string (go.InterfaceType []) m M k DFrac.discard as -
  · iexact HM
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
