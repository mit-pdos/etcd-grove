/-
The package-initialization instance of `github.com/prometheus/client_model/go`'s names-only translation: fact `True`
(prove-ps2-metrics, 2026-11-22: the package of the type of a prometheus metric's field, imported so
that prometheus's `counter` and `gauge` translate as structs).
-/
module

public import GeneratedProof.github_com.prometheus.client_model.go
public import Perennial.Proof.ProofPrelude

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

namespace github_com.prometheus.client_model.go

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_model.go :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_model.go :=
  build_get_is_pkg_init_wf

end github_com.prometheus.client_model.go

end init

end Perennial
