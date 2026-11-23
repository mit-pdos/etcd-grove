/-
The package fact of `math.rand` (the gryff kit, notes/dsv-gryff.md, "Hypotheses"): `True` for now, in
the shape of dsv-vr's names-only packages (`Dsverify/Proof/encoding/json/Base.lean` there); names only: its dependency part is `True` too and `GetIsPkgInitWf` constrains the package
itself only (the kit's `HYP_IMPORTS = 'none'`).
-/
module

public import Perennial.GeneratedProof.math.rand
public import Perennial.Proof.sync

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace math.rand

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The fact, names only: neither the package's own nor its imports' facts (as net/rpc's: the
kit's `HYP_IMPORTS = 'none'`, so the programs' tables stop at a hypothesis package). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.rand :=
  ⟨iprop(True), iprop(True)⟩
/-- `get_is_pkg_init` agrees with the fact at the package itself (its imports not constrained). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.rand :=
  ⟨fun g => g pkg_id.math.rand = isPkgInit (PROP := IProp GF) pkg_id.math.rand ∧ True⟩

end def_

end math.rand

end Perennial
