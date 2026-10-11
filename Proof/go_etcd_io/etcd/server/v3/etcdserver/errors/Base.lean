/-
Package initialization for `server/v3/etcdserver/errors` (names-only): `ErrNoSpace` holds a
fixed non-nil error (`errors.New` at init), which the entry applier compares the applier's
error with. An assumption about package initialization, not proved from `initialize'`, as the
others. Moved unchanged from `etcdserver/BaseApply.lean` (2026-10-11), so that the server's
txn package has it without the apply thread's translation (which reaches etcd's raft
dependency, `EtcdDeps`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.errors
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.errors

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

namespace go_etcd_io.etcd.server.v3.etcdserver.errors

/-- `etcdserver/errors`' package facts: `ErrNoSpace` is a fixed non-nil error. -/
abbrev errorsInit : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr ErrNoSpace ↦□ GoInterface.ok e)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors :=
  define_is_pkg_init errorsInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.errors

end init

end Perennial
