/-
Package initialization instances for etcd's interval tree (`pkg/v3/adt`, translated with
bodies). Its imports (`bytes`, `fmt`, `math`, `strings`) are Perennial's. The package has no
variables the proofs read, so its package fact is `True` (an assumption about package
initialization, as in the other `Base` files, not proved from `initialize'`).
-/
module

public import Code.go_etcd_io.etcd.pkg.v3.adt
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.adt
public import Perennial.Proof.bytes
public import Perennial.Proof.fmt
public import Perennial.Proof.math
public import Perennial.Proof.strings

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

namespace go_etcd_io.etcd.pkg.v3.adt

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.adt

end init

end Perennial
