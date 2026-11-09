/-
## `permSlice.Less(i, j)` (internal helper)

**Users.** `sort.Sort`.

**Proof sketch.** `bytes.Compare` of the two permissions' keys (bytes order: W0's `keyLt`).

**Changes.** New (round 1, review S6: per (type, method); the old proofs' lemmas in `Proof/.../auth/TokenSimple*.lean`, `TokenKeeperRun.lean`, `TokenNop.lean`, `PermSorter.lean`).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Internal

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

/-- **`perms.Less(i, j)`**: the keys' order. -/
def permSlice.Less.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ps : List Loc) (ks : List Bytes) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ sl ↦*{dq} ps ∗ permKeysAt ps ks ∗ ⌜sint.nat i < ps.length ∧ sint.nat j < ps.length ∧
      0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ }}
    (App (App (Val (sl @!! go_etcd_io.etcd.server.v3.auth.permSlice.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ (b : Bool), RET #b; sl ↦*{dq} ps ∗
      ⌜b = true ↔ ∃ ki kj, ks[sint.nat i]? = some ki ∧ ks[sint.nat j]? = some kj ∧ keyLt ki kj⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
