/-
The package fact of io/ioutil (notes/dsv-quepaxa.md): `Discard` holds some writer, read-only for good
(dsv-retire-3, 2026-11-26: zerolog's `New(nil)` reads it; until then `True`). Names only but
`Discard`, whose initializer (`Discard = io.Discard`) is translated with its import `io`
(dsv-retire-1-inits, 2026-11-25), so its dependencies hold `io`'s fact.
-/
module

public import Dsverify.GeneratedProof.io.ioutil
public import Perennial.Proof.io.Base
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace io.ioutil

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io.ioutil :=
  define_is_pkg_init iprop(∃ w : GoInterface, globalAddr Discard ↦□ w)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io.ioutil :=
  build_get_is_pkg_init_wf

end def_

end io.ioutil
end Perennial
