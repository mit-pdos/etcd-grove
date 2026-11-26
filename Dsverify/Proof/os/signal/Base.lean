/-
The package fact of `os.signal`: `True` (no model: notes/dsv-rabia.md). Names only but its variables
and `init` (dsv-retire-1-inits, 2026-11-25), translated with its imports `os` and `sync`, so its
dependencies hold their facts.
-/
module

public import Dsverify.GeneratedProof.os.signal
public import Proof.os.PkgInit
public import Perennial.Proof.sync.Base
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace os.signal

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.os.signal :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.os.signal :=
  build_get_is_pkg_init_wf

end def_

end os.signal
end Perennial
