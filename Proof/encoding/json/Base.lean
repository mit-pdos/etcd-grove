/-
The package fact of `encoding.json` (the encoding/json model's, names only: `True`), on its own so
that a proof over the model imports only it (mit-pdos/etcd-grove#24: the kits use the main tree's
`encoding/json`). Until 2026-11-23 in membership's `PkgInit.lean` (D43 M4, 2026-10-26: membership's
`ValidateConfigurationChange` unmarshals a conf change's context).
-/
module

public import GeneratedProof.encoding.json

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace encoding.json

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.json :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.json :=
  build_get_is_pkg_init_wf

end def_

end encoding.json
end Perennial
