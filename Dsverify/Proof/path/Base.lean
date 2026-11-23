/-
The package fact of `path` for the part `Dsverify/`: `True` (as the main tree's, which declares it in
etcd's packages; notes/dsv-rabia.md).
-/
module

public import GeneratedProof.path
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base
public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace path

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.path :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.path :=
  build_get_is_pkg_init_wf

end def_

end path
end Perennial
