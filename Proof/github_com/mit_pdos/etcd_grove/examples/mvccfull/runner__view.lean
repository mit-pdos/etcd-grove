/- Lean-first (no Rocq counterpart). The proof of `runner.view`: Draft, to come.

The outline: `history.snapshot` (it extends `Hs`); the three-index slice `st[:p.rev:p.rev]`
(`ownSlice_same_ptr_len'`), the pending map appended when it has a change.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot

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

theorem runner.view.wp_proof
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG)) :
    runner.view.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
