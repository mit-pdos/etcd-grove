/-
Port of `election_proof/proof_SoftState__equal.v` (857d09190).
-/
import EtcdGrove.Raft.ElectionProof.Spec.SoftState__equal

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem SoftState.equal.wp_proof : SoftState.equal.spec (GF := GF) (hG := hG) := by
  intro a b va vb dqa dqb
  wp_start as H
  iNamed H
  -- Lean notes: the struct-level load accessor does not fire at a general fraction, so
  -- the points-tos are split into their fields and recombined at the end.
  icases typedPointsto_not_null_dup _ _ _ $$ Ha with ⟨Ha, %Hna⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hb with ⟨Hb, %Hnb⟩
  iStructNamedSuffix Ha "_a"
  iStructNamedSuffix Hb "_b"
  wp_auto
  wp_if_destruct
  · ispecialize HΦ $$ [Lead_a RaftState_a __a Lead_b RaftState_b __b]
    · isplitl [Lead_a RaftState_a __a]
      · iapply typedPointsto_combine _ _ _ Hna
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      · iapply typedPointsto_combine _ _ _ Hnb
        simp only [TypedPointsto.typedPointstoDef]
        iframe
    iExactEq HΦ
    congr 2
    simp_all
  · ispecialize HΦ $$ [Lead_a RaftState_a __a Lead_b RaftState_b __b]
    · isplitl [Lead_a RaftState_a __a]
      · iapply typedPointsto_combine _ _ _ Hna
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      · iapply typedPointsto_combine _ _ _ Hnb
        simp only [TypedPointsto.typedPointstoDef]
        iframe
    iExactEq HΦ
    congr 2
    simp_all

end proof

end EtcdGrove
end Perennial
