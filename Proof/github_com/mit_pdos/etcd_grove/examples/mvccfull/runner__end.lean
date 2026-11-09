/- Lean-first (no Rocq counterpart). The proof of `runner.end`: Draft, to come.

The outline: for the leader with a change, `history.snapshot`'s length check against the
writer part, `history.appendRev`, the counter's `Add` (`ctrInv`); `end()` (`endCb`, at the history's
lower bound with the revision); `m.kv.Rev()` (`KV.Rev.contract` at the incarnation's invariant,
`reader_au`-like, the state `commitSt σ pend`, which the writer's half pins); `revLo`/`revHi` stored
(`m.bnd`'s halves).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__appendRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check

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

theorem runner.end.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_appendRev : history.appendRev.spec (GF := GF) (hG := hG)) :
    runner.end.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
