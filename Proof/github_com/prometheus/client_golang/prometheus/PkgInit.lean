/-
The package-initialization instance of prometheus: fact `True` (names only). One home, shared by the server's
`Base.lean` files and the WAL (until 2026-11-15 declared in the backend's `Base.lean` and the WAL's `DepsPkgInit.lean`; notes/wal-lean-integration.md).
-/
module

public import GeneratedProof.github_com.prometheus.client_golang.prometheus
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.io
public import Perennial.Proof.fmt
public import Perennial.Proof.time
public import Perennial.Proof.sync
public import Perennial.Proof.strings
public import Perennial.Proof.errors
public import Perennial.Proof.sort
public import Perennial.Proof.context
public import Perennial.Proof.bytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace github_com.prometheus.client_golang.prometheus

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  build_get_is_pkg_init_wf

end github_com.prometheus.client_golang.prometheus

end init

end Perennial
