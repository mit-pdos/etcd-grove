/-
Shared definitions of the proofs of `models.lab/jsoncodec` (JSON's syntax, which the codecs
`models/json/jsongen.py` generates and a model of `encoding/json` share): its package fact (`True`: no
variables, no imports), and `spaceB`, JSON's whitespace. Ported from dsverify-lab's
`Harness/Proof/jsoncodec/Base.lean` (`348a866`), whose `initialize'` proof is `Init.lean` here
(`etc/gen-init.py`).
-/
module

public import Net.GeneratedProof.models_lab.jsoncodec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab.jsoncodec

/-- JSON whitespace (space, tab, newline, carriage return). -/
def spaceB (c : w8) : Bool := [W8 32, W8 9, W8 10, W8 13].contains c

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.models_lab.jsoncodec :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.models_lab.jsoncodec :=
  build_get_is_pkg_init_wf

end def_

end models_lab.jsoncodec
end Perennial
