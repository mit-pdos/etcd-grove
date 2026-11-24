/-
**LOCAL, until the integration pin bump (perennial#692; delete then if Perennial has its own):** the
package initialization instance of Perennial's `internal/gomodel` (the choice and stuck points of the
standard-library Go models, `etc/gomodels.py`), which Perennial at the pin does not prove. Its fact is
`True` (the package has no variable); its `wp_initialize'` is generated (`Init.lean`,
`etc/gen-init.py`).
-/
module

public import Perennial.GeneratedProof.internal.gomodel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace internal.gomodel

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.gomodel :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.gomodel :=
  build_get_is_pkg_init_wf

end internal.gomodel

end init

end Perennial
