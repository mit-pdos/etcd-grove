/-
`c.node()` (`cursor.go`): the leaf node of the stack, materializing the path (asserts a non-empty stack). Users: `Put`, `Delete`, `Cursor.Delete`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Changes** (integration I7): also after `seek` (`curSt`'s `curPath`: `Put`, `Delete`,
`CreateBucket*` call `c.node()` right after `c.seek`), the state given back. Verify-round (A11 F9):
the post says what the callers' next step needs: the cache still represents every view it did
(`repKept`: only nodes read from pages were added), and the leaf returned is the one where the
cursor's key belongs (`keyLeaf`: the sought key after `seek`, the entry's key when positioned),
while the cursor's bucket handle is the current one at `p` (`C.gens p = gs`).

**Proof sketch.** The stack's leaf, or from its root `Bucket.node` (nil parent) and each level's
`node.childAt` (`Bucket.node` with the parent): each `repKept` (a node read from a page represents
what the page did); the stack is the search path of the key in `p`'s tree (`curPath`'s, or
`boltCur`'s position's), so its leaf is `keyLeaf`'s.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the leaf node holding the position, now cached. -/
def Cursor.node.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (T : TxView) (C : TxCore) (p : BPath) (gs : List Nat) (st : Option Nat ⊕ GoString),
  {{ curSt (GF := GF) tx γ c p gs T st ∗ ⌜st ≠ .inl none⌝ ∗ wtxCore tx γ C }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"node")) (Val #()))
  {{ (n : Loc), RET #n; curSt tx γ c p gs T st ∗ ∃ (C' : TxCore) (N : NodeR), wtxCore tx γ C' ∗
      ⌜C'.nodes n = some N ∧ N.isLeaf = true ∧ repKept C C' ∧
        (C.gens p = gs → ∀ k, curKey T p st k → keyLeaf C' p k n)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
