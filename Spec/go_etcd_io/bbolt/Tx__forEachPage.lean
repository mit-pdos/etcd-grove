/-
`tx.forEachPage(id, fn)` (`tx.go`): `fn` on the page and each descendant, depth first, with the stack of ids. Users: `Bucket.forEachPage`, the checks.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
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

/-- (internal) `fn` called on the tree's pages with its contract `P` kept. -/
def Tx.forEachPage.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (id : w64) (fn : GoFunc) (P : IProp GF),
  {{ boltTx (GF := GF) tx γ q T ∗ P ∗ □ (∀ (pg : Loc) (d : w64) (st : GoSlice) (Φ : val → IProp GF), P -∗ ▷ (P -∗ Φ #()) -∗ WP (App (App (App (Val #fn) (Val #pg)) (Val #d)) (Val #st)) {{ Φ }}) }}
    (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"forEachPage")) (Val #id)) (Val #fn))
  {{ RET #(); boltTx tx γ q T ∗ P }}

end spec

end Bbolt
end EtcdGrove
end Perennial
