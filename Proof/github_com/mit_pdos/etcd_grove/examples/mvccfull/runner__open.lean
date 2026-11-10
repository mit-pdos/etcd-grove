/- Lean-first (no Rocq counterpart). The proof of `runner.open`: Draft, to come.

The outline (the chain's step 3): `openBackend` (the opener's `K := bFresh`, `W := mvccW gx` of
`mvccW_alloc.law`), `inc_open_backend` at `k = Ops` (its `receiptBound + Ops + 4 ≤ wbInit` from
`ReceiptBoundLe 2 ^ 38` and `writerCtx`'s `Ops < 2 ^ 38`; the post's `Ops ≤ k`); `lease.NewLessor.specR` over the records (`GA := True`,
`reqOf := 3600`, the ids the live leases, `logOk_leases`; `noCluster`'s `clusterOk` from
`noCluster.Version.spec`); `mvcc.api.New.specR` at `σ` (the lessor's owner part at the live leases,
`logOk_leases`' items; the resumed compaction at `u` with the unset hook, `Pre := True`, the commit
request `True`); `SetTxPostLockInsideApplyHook` and the hook frozen (`hookIs`); `inc_alloc` with
the carried parts; the checks by `KV.Rev`, `KV.Read`, `Txn.Rev`, `Txn.FirstRev`, `Txn.End` at the new
invariant; `checkLeases`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__openBackend
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.noCluster__Version

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

theorem runner.open.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (halloc : mvccW_alloc.law (GF := GF))
    (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (wp_openBackend : runner.openBackend.spec (GF := GF) (hG := hG))
    (wp_Version : noCluster.Version.spec (GF := GF) (hG := hG))
    (wp_NewLessor : lease.NewLessor.specR (GF := GF) (hG := hG))
    (wp_mNew : mvcc.api.New.specR (GF := GF) (hG := hG))
    (wp_SetHook : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG)) :
    runner.open.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
