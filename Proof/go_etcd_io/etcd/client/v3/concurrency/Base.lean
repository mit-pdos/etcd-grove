/-
Package initialization instances for `go.etcd.io/etcd/client/v3/concurrency` (the counterpart of
`Proof/go_etcd_io/etcd/cache/v3/Base.lean`, whose instances for `clientv3`, the protobuf
packages and zap it reuses). Its standard-library imports (`context`, `errors`, `fmt`,
`strings`, `sync`, `time`, `math`) are Perennial's.

The package's facts (`concurrencyInit`): `Mutex`'s errors `ErrLocked`, `ErrSessionExpired`,
`ErrLockReleased` and `Election`'s `ErrElectionNotLeader`, `ErrElectionNoLeader` hold fixed
non-nil errors (`Session` reads no package-level variable). As in the cache's `Base.lean`, this is an assumption about package initialization,
not proved from `initialize'`.
-/
module

public import Code.go_etcd_io.etcd.client.v3.concurrency
public import GeneratedProof.go_etcd_io.etcd.client.v3.concurrency
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.strings
public import Perennial.Proof.math

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.client.v3.concurrency

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's facts: `Mutex`'s three errors (`ErrLocked`, `ErrSessionExpired`,
`ErrLockReleased`) and `Election`'s two (`ErrElectionNotLeader`, `ErrElectionNoLeader`) each hold
a fixed non-nil error (`errors.New`), for good. -/
abbrev concurrencyInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrLocked ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrSessionExpired ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrLockReleased ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrElectionNotLeader ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrElectionNoLeader ↦□ GoInterface.ok e))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  define_is_pkg_init concurrencyInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.client.v3.concurrency

end Perennial
