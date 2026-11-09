/- Lean-first (no Rocq counterpart). The proof of `runner.gen`: Draft, to come.

The outline: `pick` of `Mix.Op`; per kind, `genKey`, `genEnd`, `newVal`, `genLease`,
`genSubs`, `genRange`, `choose`, `pick` of `Mix.CompactAt`; the struct allocated, its slices
persisted (`opIs`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newVal
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genSubs

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

theorem runner.gen.wp_proof
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_newVal : runner.newVal.spec (GF := GF) (hG := hG))
    (wp_genLease : runner.genLease.spec (GF := GF) (hG := hG))
    (wp_genEnd : runner.genEnd.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genSubs : runner.genSubs.spec (GF := GF) (hG := hG))
    (wp_genRange : runner.genRange.spec (GF := GF) (hG := hG)) :
    runner.gen.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
