/-
Package initialization instance for etcd's `server/v3/lease/leasehttp` (names only; the
lease-renew plan, 2026-11-01): `EtcdServer.LeaseRenew` forwards a renewal to the leader at
`url + LeasePrefix` (`RenewHTTP`, a contract). Its fact: `LeasePrefix` holds some string, read-only
(`http.go`: `"/leases"`; the value is not stated, as no spec needs it). An assumption about package
initialization (`Init.lean`'s trust-boundary axiom `LeasePrefix_init`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.lease.leasehttp
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasehttp
public import Proof.go_etcd_io.etcd.server.v3.lease.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.lease.leasehttp

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp :=
  define_is_pkg_init iprop(∃ p : GoString, globalAddr LeasePrefix ↦□ p)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.lease.leasehttp

end init

end Perennial
