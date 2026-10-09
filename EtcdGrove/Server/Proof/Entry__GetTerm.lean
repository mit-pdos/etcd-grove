/-
Proof of `Spec/Entry__GetTerm.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Server.Spec.Entry__GetTerm

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

theorem raftpb.Entry.GetTerm.wp_proof : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG) := by
  intro e m
  wp_start as #He
  iunfold entryAt at He
  icases He with ⟨%Hnn, %pt, %pi, %pty, %d, #Ht, #Hpt, #Hi, #Hpi, #Hty, #Hpty, #Hd, #Hds⟩
  have hd : decide (e = null) = false := decide_eq_false Hnn
  wp_auto
  simp only [hd, Bool.not_false]
  wp_auto
  iunfold optU64 at Hpt
  by_cases hp : pt = null
  · rw [if_pos hp]
    icases Hpt with %Hz
    subst hp
    (try wp_auto)
    rw [← Hz]
    iapply HΦ
    itrivial
  · rw [if_neg hp]
    (try wp_auto)
    have hd' : decide (pt = null) = false := decide_eq_false hp
    simp only [hd', Bool.not_false]
    wp_auto
    iapply HΦ
    itrivial


end proof

end EtcdGrove
end Perennial
