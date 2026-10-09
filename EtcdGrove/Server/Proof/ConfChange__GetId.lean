/-
Proof of `Spec/ConfChange__GetId.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Server.Spec.ConfChange__GetId

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3


section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

theorem raftpb.ConfChange.GetId.wp_proof :
    raftpb.ConfChange.GetId.spec (GF := GF) (hG := hG) := by
  intro cc v dq id
  wp_start as ⟨Hcc, #Hid⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hcc
  have hd : decide (cc = null) = false := decide_eq_false Hnn
  iStructNamed Hcc
  wp_auto
  simp only [hd, Bool.not_false]
  wp_auto
  iunfold optU64 at Hid
  by_cases hp : v.Id' = null
  · rw [if_pos hp]
    icases Hid with %Hz
    rw [hp]
    (try wp_auto)
    rw [← Hz]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [hp]
    iframe
  · rw [if_neg hp]
    (try wp_auto)
    have hd' : decide (v.Id' = null) = false := decide_eq_false hp
    simp only [hd', Bool.not_false]
    wp_auto
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end EtcdGrove
end Perennial
