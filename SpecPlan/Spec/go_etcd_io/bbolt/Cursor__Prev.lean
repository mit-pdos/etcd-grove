/-
`c.Prev()` (`cursor.go`).

**Users.** None in etcd. Snippet: `ReqNested`.

**Proof sketch.** `prev`: pop levels at their first element, step back, descend to the last
element. **Scoped to read transactions** (unchanged): in a write transaction whose deletes emptied a
leaf node, `Prev` returns nil in the middle of the bucket (`issues/bbolt-cursor-prev-empty-leaf.md`),
which no true spec over `T.ents` can state without the node layout.

**Changes.** Unchanged (over paths).
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The handle premise `bktUse`
(new: without the generations, a deleted and re-created bucket can leave the view as it was, and the
cursor must not survive its bucket), given back; the cursor names its handle `b` in place of `gs`
(the per-path generation counter it replaces was unobservable state, redundant with ownership).
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

/-- `c.Prev()` in a read transaction: the previous entry; at the first entry or unpositioned, nil
and nil. -/
def Cursor.Prev.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c b p T pos ∗ bktUse tx γ T.rw b p qb ∗ ⌜T.rw = false⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Prev")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); bktUse tx γ T.rw b p qb ∗ boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c b p T none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some 0 => iprop(boltCur tx γ c b p T (some 0) ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some (i + 1) => iprop(boltCur tx γ c b p T (some i) ∗ curAt tx γ (T.ents p) i k v)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
