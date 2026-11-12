/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.resyncDelay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.resyncDelay.wp_proof : mvcc.resyncDelay.spec (GF := GF) (hG := hG) := by
  intro d last now
  wp_start
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hper, -⟩
  wp_auto
  have hp : (0 : Int) < sint.Z (W64 100000000) := by decide
  wp_if_destruct
  · iapply HΦ; ipureintro
    exact ⟨by rw [ite_eq_right_iff.2 (fun h => absurd rfl h.1)], hp⟩
  wp_if_destruct
  · wp_if_destruct
    · iapply HΦ; ipureintro; simp_all
    · iapply HΦ; ipureintro
      rename_i Hd
      exact ⟨by rw [ite_eq_right_iff.2 (fun h => absurd h.2.2 (by word))], hp⟩
  · iapply HΦ; ipureintro
    rename_i Hl
    exact ⟨by rw [ite_eq_right_iff.2 (fun h => absurd h.2.1 (by omega))], hp⟩

end proof

end EtcdGrove
end Perennial
