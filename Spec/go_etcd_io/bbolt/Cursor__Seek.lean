/-
`c.Seek(key)` (`cursor.go`): positions at the first entry whose key is not below `key`.

**Users.** The backend's ranges (`batch_tx.go:218`: `Seek` then `Next` while below the end key; the
same in read transactions), defrag's catch-up. Snippets: `ReqBackendBatch`, `ReqBackendRead`.

**Proof sketch.** `seek`: search from the root (binary search in each page or node, 4d's element
reads), then, past the last element of a leaf, `next`. `seekIdx` of the entries.

**Changes.** Repositioning at the current view; over paths and nested buckets.
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

/-- `c.Seek(key)`: repositions the cursor at the first entry not below `key` in the current view. -/
def Cursor.Seek.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat) (T' : TxView) (key : GoSlice)
    (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T' ∗ boltCur tx γ c p gs T pos ∗ key ↦*{dk} kb ∗ ⌜T'.gens p = gs⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Seek")) (Val #key))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T' ∗ key ↦*{dk} kb ∗
      boltCur tx γ c p gs T' (some (seekIdx (T'.ents p) kb)) ∗
      curAt tx γ (T'.ents p) (seekIdx (T'.ents p) kb) k v }}

end spec

end Bbolt
end EtcdGrove
end Perennial
