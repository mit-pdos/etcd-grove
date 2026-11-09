/- Lean-first (no Rocq counterpart). The proof of `runner.txn`: Draft, to come.

The outline: as mvccrand's `writer.txn`, at the incarnation's invariant (`reader_au`-like
updates with the writer's `m.σ` half pinning the state): `KV.Read` (either mode), `Txn.Rev`,
`Txn.FirstRev`, `history.snapshot`, `NewReadOnlyTxnWrite`, `Txn.Range` and `checkRangeAt`, `Txn.End`;
or `begin`, `KV.Write` (the hook, `hookOk`), `checkHook`, `Txn.Rev`, `writeRange`, `writeSub` per
sub-operation (`subsOk` gives each `subFresh`), `Txn.Changes`, `end`. The trace `traceutil.TODO()`
makes (`ownTrace t true`) is lent to `KV.Write` and threaded through `writeRange` and each
`writeSub` (their specs take and give back `ownTrace`), as mvccrand's `writeOp` threads it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__txn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeSub
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.txn.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_roTxn : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG))
    (wp_begin : runner.begin.spec (GF := GF) (hG := hG))
    (wp_checkHook : runner.checkHook.spec (GF := GF) (hG := hG))
    (wp_writeRange : runner.writeRange.spec (GF := GF) (hG := hG))
    (wp_writeSub : runner.writeSub.spec (GF := GF) (hG := hG))
    (wp_end : runner.end.spec (GF := GF) (hG := hG)) :
    runner.txn.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
