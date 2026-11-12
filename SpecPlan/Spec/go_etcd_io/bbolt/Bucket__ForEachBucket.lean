/-
`b.ForEachBucket(fn)` (`bucket.go`): `fn(k)` for each nested bucket's key in key order, stopping at
the first error.

**Users.** `DeleteBucket` (its recursion), nested-bucket clients. Snippet: `ReqNested`.
**Proof sketch.** As `ForEach`, skipping the entries without the bucket flag. **Changes.** New.

**Re-review (N2): `spec_del`, the internal variant `DeleteBucket`'s recursion uses**
(`bucket.go:305-312`: `child.ForEachBucket(func(k) { return child.DeleteBucket(k) })`). The
callback changes the view at and below the bucket (`TxView.sameAt`: it deletes nested buckets of
`p`), which the public spec (the view fixed, any fraction) cannot carry; and Go's cursor may skip a
nested bucket after a delete in a materialized leaf (`issues/bbolt-deletebucket-nested-leak.md`,
etcd-io/bbolt#1305), so the callback is called on an increasing subsequence of `ks`, and success
ends at some loop index. Over all of the transaction (a write transaction's). Its proof is the
public one's loop with the view existential, the cursor's keys a subsequence of `ks` (deletes
remove keys at `p` and add none; the deleted inodes' key bytes stay valid). A second spec of one
function, internal and for one caller: the public spec is not an instance of it (its fraction is
any `q`), recorded as a margin of the one-spec rule for internals.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The handle premise `bktUse`
in place of `bktH … gs` and the generation check, given back (`spec_del` lends it to the callback,
which calls `DeleteBucket` on the same handle); the names are `TxView.bktNames` (the per-path
generation counter it replaces was unobservable state, redundant with ownership).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api
public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

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

/-- `b.ForEachBucket(fn)`: calls `fn` on each nested bucket's name in the bucket at `p` (the names
`ks`, in key order), carrying `I` and stopping at the first error. -/
def Bucket.ForEachBucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF) (ks : List GoString),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb ∗
      ⌜ks = T.bktNames p⌝ ∗ I 0 ∗
      □ (∀ (i : Nat) (kb : GoString) (k : GoSlice) (Φ : val → IProp GF),
          ⌜ks[i]? = some kb⌝ -∗ I i -∗ txBytes tx γ k kb -∗ boltTx tx γ q T -∗
          ▷ (∀ err : GoInterface, boltTx tx γ q T -∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) -∗
              Φ #err) -∗
          WP (App (Val #fn) (Val #k)) {{ Φ }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
  {{ (err : GoInterface), RET #err; bktUse tx γ T.rw b p qb ∗ boltTx tx γ q T ∗
      ((⌜err = GoInterface.nil⌝ ∗ I ks.length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < ks.length⌝ ∗ E i err)) }}

/-- (internal) `b.ForEachBucket(fn)` whose `fn` may change the view at and below `p`
(`DeleteBucket`'s recursion): `fn` is called on an increasing subsequence of the nested buckets'
names `ks` (index `j ≥` the loop's `i`), with all of the transaction at a view `sameAt` the first;
the result is such a view and the loop state at some index, or the callback's error. -/
def Bucket.ForEachBucket.spec_del : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (b : Loc) (p : BPath) (qb : Qp)
    (fn : GoFunc) (I : Nat → TxView → IProp GF) (E : GoInterface → TxView → IProp GF)
    (ks : List GoString),
  {{ boltTx (GF := GF) tx γ 1 T ∗ bktUse tx γ T.rw b p qb ∗
      ⌜ks = T.bktNames p⌝ ∗ I 0 T ∗
      □ (∀ (i j : Nat) (kb : GoString) (k : GoSlice) (T' : TxView) (Φ : val → IProp GF),
          ⌜i ≤ j ∧ ks[j]? = some kb ∧ T.sameAt T' p⌝ -∗ I i T' -∗ txBytes tx γ k kb -∗
          boltTx tx γ 1 T' -∗ bktUse tx γ T.rw b p qb -∗
          ▷ (∀ (err : GoInterface) (T'' : TxView), ⌜T.sameAt T'' p⌝ -∗ boltTx tx γ 1 T'' -∗
              bktUse tx γ T.rw b p qb -∗
              ((⌜err = GoInterface.nil⌝ ∗ I (j + 1) T'') ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E err T'')) -∗
              Φ #err) -∗
          WP (App (Val #fn) (Val #k)) {{ Φ }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
  {{ (err : GoInterface), RET #err; bktUse tx γ T.rw b p qb ∗
      ∃ T' : TxView, ⌜T.sameAt T' p⌝ ∗ boltTx tx γ 1 T' ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ i : Nat, I i T') ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E err T')) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
