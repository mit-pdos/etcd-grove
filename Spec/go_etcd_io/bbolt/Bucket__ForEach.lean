/-
`Bucket.ForEach` (bbolt): its spec in bbolt's API (the vocabulary in `Spec/go_etcd_io/bbolt/Api.lean`),
converging on `SpecPlan/Spec/go_etcd_io/bbolt/Bucket__ForEach.lean` (auth-schema-srv port, 2026-11-19,
`notes/auth-schema-srv-port-scope.md` §4: the one spec of `Bucket.ForEach`, for both kinds of
transaction, as `Bucket.Cursor`'s; it replaces the backend layer's axioms `Bucket.ForEach_kvr`/`_kvw`).
Proof: `Proof/go_etcd_io/bbolt/Bucket__ForEach.lean`, from `Bucket.Cursor`, `Cursor.First` and
`Cursor.Next`.

**Users.** The backend's `unsafeForEach` (`batch_tx.go`), through `UnsafeForEach` of the read and
batch transactions. Evidence of the visitor's contract: `examples/bbolt/foreachkv` (Go tests).
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.ForEach(fn)` of a current handle of the bucket `n` (entries `bktEnts m`), any fraction `q` of
either kind of transaction: `fn` runs on the entries in key order (`curAt`: the `i`-th key and value,
a nested bucket's value nil), with the caller's invariant `I i` before the `i`-th; it returns the
first non-nil error `fn` returned (`E i err` of the entry it stopped at), else nil (every entry was
visited, `I` of their count). `fn` gets the transaction at the walk's fraction and view and must give
it back at the same view (Go: "must not modify the bucket"; a change of the transaction changes its
view, so a visitor that modifies the bucket cannot meet its contract). -/
abbrev Bucket.ForEach.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView)
    (b : Loc) (n : GoString) (m : BktData) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF),
  {{ boltTx (GF := GF) tx γ q T ∗ boltBkt tx γ b n (T.gen n) ∗ ⌜T.cur.lookup n = some m⌝ ∗ I 0 ∗
      □ (∀ (i : Nat) (k v : GoSlice),
          {{ ⌜i < (bktEnts m).length⌝ ∗ I i ∗ curAt tx γ (bktEnts m) i k v ∗ boltTx tx γ q T }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; boltTx tx γ q T ∗
              ((⌜err = interface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ interface.nil⌝ ∗ E i err)) }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; boltTx tx γ q T ∗
      ((⌜err = interface.nil⌝ ∗ I (bktEnts m).length) ∨
       (∃ i : Nat, ⌜err ≠ interface.nil ∧ i < (bktEnts m).length⌝ ∗ E i err)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
