/-
`c.First()` (`cursor.go`): positions at the first entry (a nested bucket's with a nil value).

**Users.** `backend.Hash` and defrag over the root cursor (`backend.go:432, 821`), `ForEach`.
Snippets: `ReqHash`, `ReqDefrag`.

**Proof sketch.** Reset the stack, push the root (page or node, `Bucket.pageNode`), descend to the
first leaf (`goToFirstElementOnTheStack`); an empty leaf (a writer's, after deletes) is skipped by
`next` (boltdb/bolt#450's fix). The entries of `T'` at `p` in order, by the abstraction relation.

**Changes.** May reposition a cursor made at an older view (Go: "reposition your cursor after
mutating data"), given its bucket is still current; over paths.
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

/-- `c.First()`: repositions the cursor at the first entry of the bucket at `p` in the current view
`T'` (its bucket still current). -/
def Cursor.First.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat) (T' : TxView),
  {{ boltTx (GF := GF) tx γ q T' ∗ boltCur tx γ c p gs T pos ∗ ⌜T'.gens p = gs⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"First")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T' ∗
      boltCur tx γ c p gs T' (some 0) ∗ curAt tx γ (T'.ents p) 0 k v }}

end spec

end Bbolt
end EtcdGrove
end Perennial
