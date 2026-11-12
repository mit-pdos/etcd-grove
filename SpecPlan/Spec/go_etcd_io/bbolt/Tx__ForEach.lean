/-
`tx.ForEach(fn)` (`tx.go`): `fn(name, b)` for each top-level entry in key order, with the
bucket's handle (`tx.root.Bucket(name)`, nil for a value, which etcd never puts at the root).

**Users.** None in etcd (it iterates with `tx.Cursor()`). Snippet: `ReqNested`.
**Proof sketch.** `Bucket.ForEach.spec` on the root, whose callback calls `Bucket.Bucket.spec` (a
writer's child cache: all of the transaction; in a write transaction with the bucket's token,
taken from the loop's and given back to it: a share for a cached bucket, which `tx.root.Bucket`
only reads, `tx.go:157-160`, the whole for one it caches). **Changes.** New.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** In a write transaction the
whole tokens of the top-level buckets (`os`: their cache entries) are taken, each lent to the
callback at its handle, and given back with the cache entries of the buckets visited filled; in
place of `bktH … gs` (the per-path generation counter it replaces was unobservable state, redundant
with ownership).
**Changes (2026-11-12, the review's finding 4).** A share `qs k` of a cached bucket's token
(`os k = some _`: the lookup only reads the cache), the whole only for one not cached yet.
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

/-- `tx.ForEach(fn)`: calls `fn` on each top-level bucket's name and handle in key order, carrying
`I` and stopping at the first error. -/
def Tx.ForEach.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (os : GoString → Option Loc)
    (qs : GoString → Qp) (fn : GoFunc) (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  {{ boltTx (GF := GF) tx γ q T ∗ ⌜T.rw = true → q = 1⌝ ∗ I 0 ∗
      (if T.rw then iprop([∗list] k ∈ T.bktNames [], bktOwn tx γ [k] (os k) (qs k) ∗
          ⌜os k = none → qs k = 1⌝) else iprop(emp)) ∗
      □ (∀ (i : Nat) (kb : GoString) (vo : Option GoString) (k : GoSlice) (bl : Loc)
          (Φ : val → IProp GF),
          ⌜(T.ents [])[i]? = some (kb, vo)⌝ -∗ I i -∗ txBytes tx γ k kb -∗
          (match vo with
           | none => iprop(⌜bl ≠ Loc.null ∧ (T.rw = true → ∀ b', os kb = some b' → bl = b')⌝ ∗
               bktUse tx γ T.rw bl [kb] (qs kb))
           | some _ => iprop(⌜bl = Loc.null⌝)) -∗
          boltTx tx γ q T -∗
          ▷ (∀ err : GoInterface, boltTx tx γ q T -∗
              (match vo with
               | none => bktUse tx γ T.rw bl [kb] (qs kb)
               | some _ => iprop(emp)) -∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) -∗
              Φ #err) -∗
          WP (App (App (Val #fn) (Val #k)) (Val #bl)) {{ Φ }}) }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; boltTx tx γ q T ∗
      (if T.rw then iprop(∃ os' : GoString → Option Loc,
          ⌜∀ k b', os k = some b' → os' k = some b'⌝ ∗
          [∗list] k ∈ T.bktNames [], bktOwn tx γ [k] (os' k) (qs k)) else iprop(emp)) ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (T.ents []).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (T.ents []).length⌝ ∗ E i err)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
