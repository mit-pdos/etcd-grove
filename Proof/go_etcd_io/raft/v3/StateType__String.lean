/-
Lean-first (no Rocq counterpart): the proof of `StateType.String`
(`Spec/go_etcd_io/raft/v3/StateType__String.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.StateType__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem StateType.String.wp_proof :
    StateType.String.spec (GF := GF) (hG := hG) := by
  intro ro
  wp_start
  ihave #HI := isInitialized_access $$ Hpkg
  iNamed HI
  wp_auto
  have Hb : 0 ≤ sint.Z (stateW64 ro) ∧ sint.Z (stateW64 ro) < 4 := by
    cases ro <;> exact ⟨by decide, by decide⟩
  have Hl : stmapV.arr[(sint.Z (stateW64 ro)).toNat]? = some (roleStr ro) := by
    cases ro <;> rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true Hb)]
  icases array_acc _ _ _ _ stmapV (roleStr ro) Hb.1 Hl $$ stmap with ⟨#Hel, -⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
