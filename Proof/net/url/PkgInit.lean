/-
The package-initialization instance of `net/url` (names only: the element type of `types.URLs`, unit
N4, 2026-10-17; zap's sink registry's factories' parameter): fact `True`. Moved out of the apply
package's `Base.lean` (prove-zap3, 2026-11-21) so that zap's instances, which import it since zap's
`_sinkRegistry` is translated, do not import the server.
-/
module

public import GeneratedProof.net.url
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

namespace net.url

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.url :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.url :=
  build_get_is_pkg_init_wf

end net.url

end init

end Perennial
