/-
The package fact of `encoding.hex` for the part `Dsverify/`: `True` (as the main tree's, which declares it in
bbolt's `PkgInit.lean`; notes/dsv-swiftpaxos.md).
-/
module

public import GeneratedProof.encoding.hex
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace encoding.hex

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.hex :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.hex :=
  build_get_is_pkg_init_wf

end def_

end encoding.hex
end Perennial
