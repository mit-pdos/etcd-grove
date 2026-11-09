/- Lean-first (no Rocq counterpart). The proof of `stream.complete`: Draft, to come (`sorry`).

The callee: `stream.expect`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__complete
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__expect

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

theorem stream.complete.wp_proof
    (wp_stream_expect : stream.expect.spec (GF := GF) (hG := hG)) :
    stream.complete.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
