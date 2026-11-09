/- Lean-first (no Rocq counterpart). The proof of `runner.shut`: Draft, to come.

The outline: `KV.Close.contract` (`mvccClosed`), `check`; `inc_census`; `lessor.Stop`;
`backend.Close.spec` (`commitReq` of `True`; at `dbCloseOk` the `nil` arm, its file `bFile`'s path
agreeing with `bkKeep`'s), `check`; `inc_stop_image`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close

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

theorem runner.shut.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hstop : mvccImage_stop.law (GF := GF))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_Stop : lease.lessor.Stop.spec (GF := GF) (hG := hG))
    (wp_bClose : backend.backend.Close.spec (GF := GF) (hG := hG)) :
    runner.shut.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
