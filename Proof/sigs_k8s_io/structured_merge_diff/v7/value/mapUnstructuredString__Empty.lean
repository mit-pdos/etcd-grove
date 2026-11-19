/-
`value.mapUnstructuredString.Empty`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty
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

theorem value.mapUnstructuredString.Empty.wp_proof :
    value.mapUnstructuredString.Empty.spec (GF := GF) := fun m kvs => by
  wp_start as Hm
  ihave Hi := isMapV_val $$ Hm
  icases isIface_map_val $$ Hi with ⟨%M, #HM, %Hk, -⟩
  have hsz := map_size_kvs M kvs Hk.1 Hk.2
  wp_auto
  wp_apply wp_map_len_lt m M DFrac.discard as ⟨-, %Hlt⟩
  · iexact HM
  wp_end
  ipureintro
  rw [decide_eq_true_iff, ← List.length_eq_zero_iff, ← hsz]
  constructor
  · intro h; word
  · intro h; rw [h]; rfl

end proof

end smd
end EtcdGrove
end Perennial
