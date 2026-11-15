/-
## `permSlice.Swap(i, j)` (internal helper)

**Users.** `sort.Sort`.

**Proof sketch.** Two element writes.

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`perms.Swap(i, j)`**. -/
def permSlice.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (i j : w64) (pi pj : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ sl ↦* ps ∗ ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ps[sint.nat i]? = some pi ∧
      ps[sint.nat j]? = some pj⌝ }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.auth.permSlice.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* ((ps.set (sint.nat i) pj).set (sint.nat j) pi) }}

end spec
end Auth
end EtcdGrove
end Perennial
