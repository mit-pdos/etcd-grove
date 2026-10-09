/-
Package initialization instances for `go.etcd.io/etcd/client/v3/concurrency` (the counterpart of
`Proof/go_etcd_io/etcd/cache/v3/Base.lean`, whose instances for `clientv3`, the protobuf
packages and zap it reuses). Its standard-library imports (`context`, `errors`, `fmt`,
`strings`, `sync`, `time`, `math`) are Perennial's.

The package's facts are `True`: `Session` reads no package-level variable (`Mutex`'s and
`Election`'s errors, `ErrLocked`, `ErrSessionExpired`, ..., will need theirs when they are
proved). As in the cache's `Base.lean`, this is an assumption about package initialization,
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

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.client.v3.concurrency

end Perennial
