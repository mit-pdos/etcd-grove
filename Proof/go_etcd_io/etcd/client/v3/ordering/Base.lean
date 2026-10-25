/-
Package initialization instances for `go.etcd.io/etcd/client/v3/ordering`.
Reuses `Proof/go_etcd_io/etcd/client/v3/concurrency/Base.lean` for `clientv3`, `grpc`, `context`,
`sync`, and `errors`, plus `Perennial.Proof.sync.atomic`.
-/
module

public import Code.go_etcd_io.etcd.client.v3.ordering
public import GeneratedProof.go_etcd_io.etcd.client.v3.ordering
public import Proof.go_etcd_io.etcd.client.v3.concurrency.Base
public import Perennial.Proof.sync.atomic

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.client.v3.ordering

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's facts: the global `ErrNoGreaterRev` holds a fixed non-nil `error`. -/
abbrev orderingInit : IProp GF :=
  iprop(∃ err : GoInterface, globalAddr ErrNoGreaterRev ↦□ err ∗ ⌜err ≠ GoInterface.nil⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering :=
  define_is_pkg_init orderingInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.client.v3.ordering

end Perennial
