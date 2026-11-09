/-
`c.node()` (`cursor.go`): the leaf node of the stack, materializing the path (asserts a non-empty stack). Users: `Put`, `Delete`, `Cursor.Delete`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Changes** (integration I7): also after `seek` (`curSt`'s `curPath`: `Put`, `Delete`,
`CreateBucket*` call `c.node()` right after `c.seek`), the state given back.
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
  {{ (n : Loc), RET #n; curSt tx γ c p gs T st ∗ ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜∃ N, C'.nodes n = some N ∧ N.isLeaf = true⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
