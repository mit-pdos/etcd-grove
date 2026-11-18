/-
The package fact of `client/pkg/v3/verify` for the part `LinuxFs/` (the main tree's translation, with
`Assert`'s body): `True`, as the main tree's (whose instance is in the backend's `Base`, over the main
`os`, which the part cannot import). WAL W6, 2026-11-13.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.fmt
public import Perennial.Golang.Theory
public import Code.go_etcd_io.etcd.client.pkg.v3.verify
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.client.pkg.v3.verify

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify :=
  define_is_pkg_init iprop(True)

end go_etcd_io.etcd.client.pkg.v3.verify

end init

end Perennial
