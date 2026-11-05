/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

Strict M1 (2026-11-05): restated over mvcc's API; the proof is a placeholder until the statement
gap it rests on is closed (gap A). The proof over mvcc's internals is in the history (before
`645402be7a`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange
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

theorem txn.deleteRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    : txn.deleteRange.spec (GF := GF) (hG := hG) := by
  sorry -- M1-REPLACE: gap A: `Txn.Range`'s outcome is over the index's answers and nothing gives `LogOk` of the read log (the per-revision change bound), notes/mvcc-migration/txn.md (and `delKeys_client` for the deletes)

end proof

end EtcdGrove
end Perennial
