/-
Shared definitions of the proofs of `netmodels.lab/pbcodec` (protobuf's wire format, which the
codecs `etc/pbgen.py` generates call): its package fact (`True`: no variables, no imports).
-/
module

public import Net.GeneratedProof.netmodels_lab.pbcodec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace netmodels_lab.pbcodec

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.netmodels_lab.pbcodec :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.netmodels_lab.pbcodec :=
  build_get_is_pkg_init_wf

end def_

end netmodels_lab.pbcodec
end Perennial
