/-
`b.ForEach(fn)` (`bucket.go`): `fn(k, v)` for each entry in key order (a nested bucket's with a nil
value), stopping at `fn`'s first error.

**Users.** The backend's `UnsafeForEach` (`batch_tx.go:256`, `tx_buffer.go:133`), `backend.Hash`
(`:438`), defrag's copy (`:833, 913`: `fn` puts into another database's transaction). Snippets:
`ReqHash`, `ReqDefrag`.

**Proof sketch.** `Cursor.First.spec`, then `Cursor.Next.spec` until a nil key: `fn` is called with
the `i`-th entry (`curAt`) and the transaction at the same view (its contract gives it back
unchanged, so the cursor stays valid); the loop carries `I i`.

**Changes.** New.

**Margin.** `fn` must not change the transaction (Go: "must not modify the bucket").
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

/-- `b.ForEach(fn)`: calls `fn` on each entry of the bucket at `p` in key order, carrying `I`
(entries done) and stopping at the first error (`E i err`); `fn` gets the transaction and gives it
back unchanged. -/
def Bucket.ForEach.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ ⌜T.gens p = gs⌝ ∗ I 0 ∗
      □ (∀ (i : Nat) (k v : GoSlice) (Φ : val → IProp GF),
          ⌜i < (T.ents p).length⌝ -∗ I i -∗ curAt tx γ (T.ents p) i k v -∗ boltTx tx γ q T -∗
          ▷ (∀ err : GoInterface, boltTx tx γ q T -∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) -∗
              Φ #err) -∗
          WP (App (App (Val #fn) (Val #k)) (Val #v)) {{ Φ }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; boltTx tx γ q T ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (T.ents p).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (T.ents p).length⌝ ∗ E i err)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
