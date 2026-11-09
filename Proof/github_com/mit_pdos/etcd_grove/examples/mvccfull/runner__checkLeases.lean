/- Lean-first (no Rocq counterpart). The proof of `runner.checkLeases`: Draft, to come.

The outline: as mvccrand's `writer.checkLeases` over `lessorW` (`GetLease` through
`isLessor`'s clause or `lessor.GetLease.spec`, the owner's items `pendItems σ.log []` matching the
model's last state; `Leases`'s count against the live set; `Lookup`, `Lease.Keys`, `sort.Strings`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__GetLease
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Leases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys
public import Perennial.Spec.sort.Strings

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

theorem runner.checkLeases.wp_proof
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_GetLease : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_Leases : lease.lessor.Leases.spec (GF := GF) (hG := hG))
    (wp_Lookup : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (wp_Keys : lease.Lease.Keys.spec (GF := GF) (hG := hG))
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG)) :
    runner.checkLeases.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
