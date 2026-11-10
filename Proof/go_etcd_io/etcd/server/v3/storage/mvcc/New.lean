/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncWatchersLoop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncVictimsLoop
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas

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

/-- Two of the reader slots out of `n ≥ 2`. -/
theorem mvcc.slots_take2 (Q : IProp GF) (n : Nat) (h : 2 ≤ n) :
    ([∗list] _x ∈ List.replicate n (), Q) ⊢
      Q ∗ Q ∗ [∗list] _x ∈ List.replicate (n - 2) (), Q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega, List.replicate_succ, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
  iframe

theorem mvcc.New.wp_proof
    (hNew : mvcc.newWatchableStore.spec (GF := GF) (hG := hG))
    (hSWL : mvcc.watchableStore.syncWatchersLoop.spec (GF := GF) (hG := hG))
    (hSVL : mvcc.watchableStore.syncVictimsLoop.spec (GF := GF) (hG := hG)) :
    mvcc.New.spec (GF := GF) (hG := hG) := by
  -- B3 Prove (mvccfull's Freeze, 2026-11-10): over `newWatchableStore.spec`'s restated pre; the
  -- closer `wsCloserM … r.crev` from `storeCloserM` and the stop channel's closer, as the fresh proof
  -- (commit `ae30739dde`, this file) made `wsCloser`.
  sorry

end proof

end EtcdGrove
end Perennial
