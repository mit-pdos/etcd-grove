/- Lean-first (no Rocq counterpart). The proof of `stream.act`: Draft, to come (`sorry`).

The callees in call order: `pick` (the weights), `watch`, `cancel`, `stream.pick`,
`RequestProgress`, `RequestProgressAll`, `Rev` (through `shapes.law`), `inBounds`, `genKey`
`context.TODO`, `Watch`, `check`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__act
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__watch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__cancel
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
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

theorem stream.act.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF))
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_stream_watch : stream.watch.spec (GF := GF) (hG := hG))
    (wp_stream_cancel : stream.cancel.spec (GF := GF) (hG := hG))
    (wp_stream_pick : stream.pick.spec (GF := GF) (hG := hG))
    (wp_inBounds : inBounds.spec (GF := GF) (hG := hG))
    (wp_runner_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    stream.act.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
