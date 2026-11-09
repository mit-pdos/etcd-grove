/-
`tx.Cursor()` (`tx.go`): `tx.root.Cursor()`, a cursor over the top-level bucket names (nil values).

**Users.** `backend.Hash` (`backend.go:431`), defrag (`:818, 889, 979`). Snippets: `ReqHash`,
`ReqDefrag`. **Proof sketch.** `Bucket.Cursor.spec` on the root bucket (`tx.root`, the path `[]`,
whose generation no `DeleteBucket` bumps). **Changes.** New.
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `tx.Cursor()`: an unpositioned cursor over the root bucket. -/
def Tx.Cursor.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView),
  {{ boltTx (GF := GF) tx γ q T }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; boltTx tx γ q T ∗ boltCur tx γ c [] (T.gens []) T none }}

end spec

end Bbolt
end EtcdGrove
end Perennial
