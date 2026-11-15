/-
`c.Next()` (`cursor.go`).

**Users.** The backend's ranges (`batch_tx.go:218`), `Hash` and defrag's root iteration, `ForEach`.
Snippets: `ReqBackendBatch`, `ReqHash`.

**Proof sketch.** `next`: pop exhausted levels, step, descend to the first element; empty pages are
skipped. At the end the stack stays at the last leaf past its end (a further `Next` returns nil
again).

**Changes.** Unchanged (over paths); the transaction must still be at the view the cursor was
positioned at.
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

/-- `c.Next()`: the next entry (nil and nil at the end, where the cursor stays); unpositioned: nil. -/
def Cursor.Next.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c b p T pos ∗ bktUse tx γ T.rw b p qb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); bktUse tx γ T.rw b p qb ∗ boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c b p T none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some i => iprop(
           boltCur tx γ c b p T (some (if i + 1 < (T.ents p).length then i + 1 else i)) ∗
           curAt tx γ (T.ents p) (i + 1) k v)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
