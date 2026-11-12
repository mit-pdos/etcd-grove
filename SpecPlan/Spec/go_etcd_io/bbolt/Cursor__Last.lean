/-
`c.Last()` (`cursor.go`). **Users.** None in etcd. Snippet: `ReqNested`.

**Proof sketch.** As `First`, descending to the last leaf. In a write transaction whose bucket's
leaves were all emptied by deletes it loops forever (`issues/bbolt-cursor-last-empty-leaves-hang.md`):
a hang is no counterexample to the triple (partial correctness).

**Changes.** Repositioning at the current view; over paths.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- `c.Last()`: repositions the cursor at the last entry of the bucket at `p` in the current view
(nil and nil if it is empty). -/
def Cursor.Last.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat) (T' : TxView),
  {{ boltTx (GF := GF) tx γ q T' ∗ boltCur tx γ c p gs T pos ∗ ⌜T'.gens p = gs⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Last")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T' ∗
      boltCur tx γ c p gs T' (some ((T'.ents p).length - 1)) ∗
      curAt tx γ (T'.ents p) ((T'.ents p).length - 1) k v }}

end spec

end Bbolt
end EtcdGrove
end Perennial
