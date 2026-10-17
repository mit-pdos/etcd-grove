/-
Package initialization for `pkg/v3/ioutil` (readcloser.go with bodies, the rest names only;
branch `pr-verify/etcd-21569`): `ErrShortRead` and `ErrExpectEOF` hold fixed non-nil errors
(`fmt.Errorf` without `%w` at init: pointer errors, `errors.IsPointerError`), which the exact
reader returns. An assumption about package initialization, not proved from `initialize'`, as
the others (`etcdserver/errors/Base.lean`).
-/
module

public import Code.go_etcd_io.etcd.pkg.v3.ioutil
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.ioutil
public import Perennial.Proof.errors
public import Perennial.Proof.io
public import Perennial.Proof.fmt

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

namespace go_etcd_io.etcd.pkg.v3.ioutil

/-- `ioutil`'s package facts: `ErrShortRead` and `ErrExpectEOF` are fixed non-nil errors
(pointer errors). -/
abbrev ioutilInit : IProp GF :=
  iprop(∃ e1 e2 : GoInterfaceOk, globalAddr ErrShortRead ↦□ GoInterface.ok e1 ∗
    globalAddr ErrExpectEOF ↦□ GoInterface.ok e2 ∗
    ⌜_root_.Perennial.errors.IsPointerError e1 ∧ _root_.Perennial.errors.IsPointerError e2⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil :=
  define_is_pkg_init ioutilInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.ioutil

end init

end Perennial
