/-
The package-initialization predicates of the specs-only branch.

`isPkgInit pkg_id.X` (Perennial) is the persistent fact that package `X` and its dependencies are
initialized; its user part is `pkgInitDef pkg_id.X`, opaque: what a package's globals satisfy after
its initializer runs is stated where a spec needs it, as a law `X.init.spec` of that package (an
obligation on the package's initializer, like every other spec here). The instances are generated
per package by `etc/gen-specs-pkginit.py` (`Spec/PkgInit/<pkg path>.lean`); a spec of package `X`
imports `Spec.PkgInit.<X>` for `isPkgInit pkg_id.X`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section
noncomputable section

namespace Perennial
namespace EtcdGrove
namespace PkgInit
open Iris Iris.BI

section
variable [GooseExts] [GooseSemantics] [GooseInterp] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- What package `p`'s globals satisfy once its initializer has run (opaque; see the header). -/
opaque pkgInitDef (p : GoString) : IProp GF := iprop(True)
end

end PkgInit
end EtcdGrove
end Perennial
