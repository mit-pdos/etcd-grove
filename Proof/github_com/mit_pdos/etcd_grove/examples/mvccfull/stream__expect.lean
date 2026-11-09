/- Lean-first (no Rocq counterpart). The proof of `stream.expect`: Draft, to come (`sorry`).

The callees in call order: `history.changesAt`, `watcher.matches`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__expect
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__changesAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.watcher__matches

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

theorem stream.expect.wp_proof
    (wp_history_changesAt : history.changesAt.spec (GF := GF) (hG := hG))
    (wp_watcher_matches : watcher.matches.spec (GF := GF) (hG := hG)) :
    stream.expect.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
