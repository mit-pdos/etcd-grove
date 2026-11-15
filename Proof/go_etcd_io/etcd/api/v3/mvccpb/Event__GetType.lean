/-
Proof of `Spec/go_etcd_io/etcd/api/v3/mvccpb/Event__GetType.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event__GetType

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.mvccpb.Assumptions]

theorem mvccpb.Event.GetType.wp_proof : mvccpb.Event.GetType.spec (GF := GF) (hG := hG) := by
  intro p t
  wp_start as ⟨%Hnn, #Hf⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · wp_end

end proof

end EtcdGrove
end Perennial
