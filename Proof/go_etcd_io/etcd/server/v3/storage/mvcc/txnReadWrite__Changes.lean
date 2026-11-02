/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Changes
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas


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

theorem mvcc.txnReadWrite.Changes.wp_proof : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG) := by
  intro trw
  wp_start
  (try wp_auto)
  iapply HΦ
  ipureintro; trivial

/-- **The candidate `Changes`** of a read-only write transaction (`specC`): none. -/
theorem mvcc.txnReadWrite.Changes.wp_proofC (hO : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.Changes.specC (GF := GF) (hG := hG) := by
  intro trw γ trace σ
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iapply (hO trw) $$ %Φ []
  · iexact Hpkg
  inext
  iintro -
  iapply HΦ
  iexact Htx

end proof

end EtcdGrove
end Perennial
