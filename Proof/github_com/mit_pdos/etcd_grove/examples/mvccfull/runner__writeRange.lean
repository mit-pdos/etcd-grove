/- Lean-first (no Rocq counterpart). The proof of `runner.writeRange`: Draft, to come.

The outline: `view`; `tw.Range` (`Txn.Range.contract` through `shapes.law`, its
`rangeOutcomeC` at the transaction's read log); `checkRangeAt` at the view's states, which match
the read log (`pendOk`, `HistRevs`), the pending map given back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
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

theorem runner.writeRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (wp_view : runner.view.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG)) :
    runner.writeRange.spec (GF := GF) (hG := hG) := by
  -- Draft's glue (2026-11-09): blocked by the spec. `Txn.Range.contract` takes and gives back the
  -- transaction's trace (`traceutil.ownTrace trace te`), which `runner.writeRange.spec` neither
  -- takes nor gives back (nor does `runner.writeSub.spec`, for `Txn.Put`/`Txn.DeleteRange`).
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
