/-
Package initialization instances for `go.etcd.io/etcd/client/v3/leasing` (the counterpart of
`Proof/go_etcd_io/etcd/client/v3/concurrency/Base.lean`, whose instances, and the cache's
`Base.lean`'s for `clientv3`, the protobuf packages, grpc and zap, it reuses). Its standard-library
imports (`bytes`, `context`, `errors`, `strings`, `sync`, `time`) are Perennial's.

The package's facts (`leasingInit`): the global `closedCh` holds a fixed channel (`init` makes it
and closes it; Go never writes `closedCh` afterwards). That it is closed is ghost state
(`closedChInit`, `Cache.lean`), kept out of the instance, as `context.isClosedchanInit` is, so
that the `IsPkgInit` instance needs no `[AllG GF]`. As in the cache's `Base.lean`, this is an
assumption about package initialization, not proved from `initialize'`.
-/
module

public import Code.go_etcd_io.etcd.client.v3.leasing
public import GeneratedProof.go_etcd_io.etcd.client.v3.leasing
public import Proof.go_etcd_io.etcd.client.v3.concurrency.Base
public import Perennial.Proof.bytes
public import Perennial.Proof.strings

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.client.v3.leasing

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's facts: the global `closedCh` holds a fixed channel, for good. -/
abbrev leasingInit : IProp GF :=
  iprop(∃ ch : GoChan, globalAddr closedCh ↦□ ch)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing :=
  define_is_pkg_init leasingInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.client.v3.leasing

end Perennial
