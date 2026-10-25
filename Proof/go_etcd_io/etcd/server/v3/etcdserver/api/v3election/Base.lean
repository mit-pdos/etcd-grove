/-
Package initialization for the Election service's server `server/v3/etcdserver/api/v3election`
and its messages `v3electionpb` (the auth plan's A3c, 2026-10-24; `notes/decisions.md`, "A3c of
the auth plan: Lock and Election"): `v3electionpb` has no facts; `v3election`'s is that
`ErrMissingLeaderKey` holds a fixed non-nil error (`errors.New`, `election.go`), which `Proclaim`
and `Resign` return for a request without a leader. Proved from `initialize'` (`Init.lean`). Lean-first (no
Rocq counterpart).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3election
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance v3electionpb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.v3electionpb :=
  define_is_pkg_init iprop(True)
instance v3electionpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.v3electionpb :=
  build_get_is_pkg_init_wf

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3election

/-- The package's fact: `ErrMissingLeaderKey` holds a fixed non-nil error (`election.go`). -/
def v3electionInit : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr ErrMissingLeaderKey ↦□ GoInterface.ok e)

instance v3electionInit_persistent : Persistent (v3electionInit (GF := GF)) := by
  unfold v3electionInit; infer_instance

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election :=
  define_is_pkg_init v3electionInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3election

end init

end Perennial
