/-
What the trust-boundary specs of Go's `path` (`Spec/path/`) are stated with. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace path

/-- **An absolute path already clean** (`path.Clean` leaves it as it is): it starts with `/`, is
not `/`, and has no empty, `.` or `..` segment and no trailing `/`; (2026-10-24, since `path` is
translated with its bodies and `Join`'s spec bounds its elements' lengths) shorter than `2^60`. -/
def PathCleanAbs [FfiSyntax] (p : GoString) : Prop :=
  go!"/" <+: p ∧ p ≠ go!"/" ∧ ¬ go!"//" <:+: p ∧ ¬ go!"/" <:+ p ∧
    k8s.dotSeg p = false ∧ k8s.dotDot p = false ∧ p.length < 2 ^ 60

end path
end EtcdGrove
end Perennial
