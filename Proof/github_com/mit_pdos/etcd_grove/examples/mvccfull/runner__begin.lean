/- Lean-first (no Rocq counterpart). The proof of `runner.begin`: Draft, to come.

The outline: `history.snapshot` (its states extend `Hs`, so its `m.rev`-th is `Hs`'s last);
`revHi.Store(m.rev + 1)` in the incarnation's invariant (`memberInv_live` with the writer's share,
`ghostVar_agree`/`update` of `m.bnd`'s halves); `copyState`; the struct allocated.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.copyState

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

theorem runner.begin.wp_proof
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_copyState : copyState.spec (GF := GF) (hG := hG)) :
    runner.begin.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
