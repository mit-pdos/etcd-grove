/-
A bytes-affine interval as the Go `Interval` (its `Comparable`s are `BytesAffineComparable`s):
what `NewBytesAffineInterval(b, e)` returns (2026-10-14, unit P2: the auth store's permission
cache queries its interval trees with these). Lean-first (no Rocq counterpart). The tree's proof
(`Defs.lean`, `ownIvt`) covers string-affine intervals only; the auth store takes its trees'
queries on bytes-affine intervals as a contract (`auth.ivtQuery`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section defs
variable [ext : FfiSyntax] [GoGlobalContext]

/-- The bytes-affine interval value `[b, e)` (slices `b`, `e`) as the Go `Interval`. -/
def bytesIvl (b e : GoSlice) : Interval :=
  { Begin' := interface.mkOk BytesAffineComparable.ty #b,
    End' := interface.mkOk BytesAffineComparable.ty #e }

end defs

end adt
end EtcdGrove
end Perennial
