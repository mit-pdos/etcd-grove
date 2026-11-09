/- Lean-first (no Rocq counterpart). The proof of `runner.genLease`: Draft, to come.

The outline: `choose(2)`, the slice's length, `choose(len)`, the element.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose

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

theorem runner.genLease.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG)) :
    runner.genLease.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
