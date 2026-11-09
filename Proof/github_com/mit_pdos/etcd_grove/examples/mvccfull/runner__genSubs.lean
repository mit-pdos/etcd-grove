/- Lean-first (no Rocq counterpart). The proof of `runner.genSubs`: Draft, to come.

The outline: `choose(3)` for the count, then per iteration `choose(3)`: `genKey`, the
checks against the puts and deletes so far (`inRange`), `newVal`, `genLease`; `genKey`, `genEnd`;
`genRange`; `append`s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genSubs
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newVal
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inRange

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

theorem runner.genSubs.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_inRange : inRange.spec (GF := GF) (hG := hG))
    (wp_newVal : runner.newVal.spec (GF := GF) (hG := hG))
    (wp_genLease : runner.genLease.spec (GF := GF) (hG := hG))
    (wp_genEnd : runner.genEnd.spec (GF := GF) (hG := hG))
    (wp_genRange : runner.genRange.spec (GF := GF) (hG := hG)) :
    runner.genSubs.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
