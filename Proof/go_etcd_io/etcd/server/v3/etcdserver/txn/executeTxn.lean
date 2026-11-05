/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

Strict M1 (2026-11-05): restated over mvcc's API; the proof is a placeholder until the statement
gap it rests on is closed (gap C). The proof over mvcc's internals is in the history (before
`645402be7a`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StartSubTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StopSubTrace
public import Spec.google_golang_org.protobuf.proto.Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.getPrevKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange
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

theorem txn.executeTxn.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hStart : traceutil.Trace.StartSubTrace.spec (GF := GF) (hG := hG))
    (hExec : txn.executeRange.spec (GF := GF) (hG := hG))
    (hStop : traceutil.Trace.StopSubTrace.spec (GF := GF) (hG := hG))
    (hSize : proto.Size.spec (GF := GF) (hG := hG))
    (hPrev : txn.getPrevKV.spec (GF := GF) (hG := hG))
    (hPut : txn.put.spec (GF := GF) (hG := hG))
    (hDel : txn.deleteRange.spec (GF := GF) (hG := hG))
    : txn.executeTxn.spec (GF := GF) (hG := hG) := by
  sorry -- M1-REPLACE: gap C: `Txn.Changes.contract` gives no `0 ≤ sint.Z chs.len`, needed for `len(txnWrite.Changes()) > 0`, notes/mvcc-migration/txn.md

end proof

end EtcdGrove
end Perennial
