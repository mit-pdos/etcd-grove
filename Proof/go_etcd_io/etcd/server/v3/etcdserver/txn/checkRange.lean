/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

Strict M1 (2026-11-05): restated over mvcc's API; the proof is a placeholder until the statement
gap it rests on is closed (gap B). The proof over mvcc's internals is in the history (before
`645402be7a`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkRange

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.checkRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    : txn.checkRange.spec (GF := GF) (hG := hG) := by
  sorry -- M1-REPLACE: gap B: the draft's `checkRange.spec` lacks `Reach σ`, needed for `FirstRev`'s `W64 σ.crev = σ.crev`, notes/mvcc-migration/txn.md

end proof

end EtcdGrove
end Perennial
