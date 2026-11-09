/- Lean-first (no Rocq counterpart). The proof of `stream.receive`: Draft, to come (`sorry`).

The callees in call order: `check`, `stream.covered`, `stream.expect`, `checkKV`, `choose`,
`context.TODO`, `Range` (through `shapes.law`), `checkStoreRange`; the facts from `recv_facts`
(`persistent`, `mvccState_reachable`, `wsRecv_ok`). The first check, `resp.Revision ≤ m.revHi`:
`readQ`'s `monoNatLbOwn m.nrev |σ.notifiedLog|` and `nrevHi_acc` at the load (`Int64.Load`) give
`|σ.notifiedLog| ≤ revHi + 1`, with clause 1's `r.rev < |σ.notifiedLog|`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__receive
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkStoreRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__covered
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__expect
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
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

theorem stream.receive.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hrok : mvcc.api.wsRecv_ok.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_stream_covered : stream.covered.spec (GF := GF) (hG := hG))
    (wp_stream_expect : stream.expect.spec (GF := GF) (hG := hG))
    (wp_checkKV : checkKV.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_runner_checkStoreRange : runner.checkStoreRange.spec (GF := GF) (hG := hG)) :
    stream.receive.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
