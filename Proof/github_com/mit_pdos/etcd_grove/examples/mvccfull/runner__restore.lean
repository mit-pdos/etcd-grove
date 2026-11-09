/- Lean-first (no Rocq counterpart). The proof of `runner.restore`: Draft, to come.

The outline: as the file header, in Go's order: `buildPath`, `newMember(2, …)`, `apply` per
operation (the history's lower bound from the leader's `histW`), the builder's `inc_retire` and
`shut`; `revHi`/`cmpHi` stored (`incW` of the follower: above the builder's, `runM_mono`);
`openBackend`, `inc_open_backend`; `lessor.Recover`; `KV.Restore.contract` (its update at the
follower's incarnation invariant: `σOf … v0.ops`, `histOkM` from `logOk_hist`, `onceUpToAll` from
`logOk_once`); `SetTxPostLockInsideApplyHook`, the hook frozen; the old backend's census
(`bkCensus` with `Restore`'s `storageRest`) and `backend.Close`; the fields; `revLo`/`cmpLo`;
`KV.Rev`, `KV.Read`, `Txn.FirstRev`, `Txn.End`; `checkLeases`; the counter.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restore
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.buildPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__openBackend
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

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

theorem runner.restore.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (halloc : mvccW_alloc.law (GF := GF))
    (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF))
    (wp_buildPath : buildPath.spec (GF := GF) (hG := hG))
    (wp_newMember : runner.newMember.spec (GF := GF) (hG := hG))
    (wp_apply : runner.apply.spec (GF := GF) (hG := hG))
    (wp_shut : runner.shut.spec (GF := GF) (hG := hG))
    (wp_openBackend : runner.openBackend.spec (GF := GF) (hG := hG))
    (wp_Recover : lease.lessor.Recover.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_SetHook : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (wp_bClose : backend.backend.Close.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG)) :
    runner.restore.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
