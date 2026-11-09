/-
## `permSlice.Len()` (internal helper)

**Users.** `sort.Sort(permSlice(...))` in `RoleGrantPermission` (Perennial's sorter contract).

**Proof sketch.** `len`.

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

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

/-- **`perms.Len()`**. -/
def permSlice.Len.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ps : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ sl ↦*{dq} ps }}
    (App (Val (sl @!! go_etcd_io.etcd.server.v3.auth.permSlice.ty @!! go!"Len")) (Val #()))
  {{ (n : w64), RET #n; sl ↦*{dq} ps ∗ ⌜sint.nat n = ps.length⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
