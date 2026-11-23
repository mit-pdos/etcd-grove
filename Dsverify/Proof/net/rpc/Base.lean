/-
The package fact of `net.rpc` (the gryff kit, notes/dsv-gryff.md, "Hypotheses"): `True` for now, in
the shape of dsv-vr's names-only packages (`Dsverify/Proof/encoding/json/Base.lean` there); names only: its dependency part is `True` too and `GetIsPkgInitWf` constrains the package
itself only, since its import closure has no instances in `Net/`.
-/
module

public import Net.GeneratedProof.net.rpc
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.rpc

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The fact, names only: neither the package's own nor its imports' facts (its closure has no
instances in `Net/`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.rpc :=
  ⟨iprop(True), iprop(True)⟩
/-- `get_is_pkg_init` agrees with the fact at the package itself (its imports not constrained). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.rpc :=
  ⟨fun g => g pkg_id.net.rpc = isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∧ True⟩

end def_

end net.rpc

end Perennial
