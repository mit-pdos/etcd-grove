/-
`Bucket.ForEach_kvr` (bbolt). `b.ForEach(fn)` in a read transaction: the visitor on each entry in key
order, stopped by its first error. The trust boundary: bbolt's key-value contract as the backend uses it
(`InvBbolt.lean`), as `Bucket.Cursor_kvr`; an axiom in `Proof/go_etcd_io/bbolt/Bucket__ForEach_kvr.lean`
(auth-schema-srv A2, 2026-11-17, the user's choice (B) via etcd-grove-03: `notes/auth-schema-srv-a2-draft.md`).
Its Go tests: `examples/bbolt/foreachkv/foreach_test.go`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.ForEach(fn)` on the read transaction's bucket `b` with entries `es`: for the caller's invariant `I`
(over the number of entries visited) and error resource `E`, given the visitor's spec — on the `i`-th entry
`e`, from `I i`, called with a non-nil key slice and a value slice holding `e`'s key and value for the
transaction's life (`txBytes`) and half of the walk's `txLive`, it returns `nil` with `I (i + 1)` or an error
with `E i err` — it returns `nil` with `I es.length`, or the first error `err` the visitor returned, at an
entry `i`, with `E i err`.

Why faithful (bbolt v1.5.0, `bucket.go:585-596`; the fork `examples/go.mod` uses, `upamanyus/bbolt@ea4cab526797`,
has the same body at `bucket.go:586-597` and a byte-identical `cursor.go`): `ForEach` checks `b.tx.db == nil` (`ErrTxClosed`: excluded, the transaction is open,
`txLive`), takes `b.Cursor()` (the transaction's statistics: `rtxStats`, as `Cursor_kvr`), and runs
`for k, v := c.First(); k != nil; k, v = c.Next()`, returning the visitor's first non-nil error (test
`TestErrorStops`) and `nil` at the end. `First`/`first` (`cursor.go:35-62`) and `Next`/`next` (`next` at `cursor.go:215-247`, which skips empty
leaves) walk the entries in key order
(`es` is `bktEnts`, sorted: `TestOrderReadTx`), each key non-nil (`Seek_kv`'s `curAt`); an empty bucket calls
no visitor (`TestEmpty`). The returned slices are "only valid for the life of the transaction" (`txBytes`).
A nested bucket's entry has `v = nil`: excluded as for `Seek_kv`/`Next_kv`. The kv contract's `Data` cannot
represent a nested bucket and no kv spec creates one (there is no `Bucket.CreateBucket_kv`), so only a file
`Open_kv`'s `fileHolds path D` premise assumes could hold one, and that premise says the file holds `D`
(etcd's buckets hold none).
What the visitor must not do, and the spec excludes:
- close the transaction (`TestVisitorRollbackPanics`: the next `Next` panics, "tx closed"): the walk keeps
  half of `txLive`, so the visitor cannot meet `Tx.Rollback_kv`'s `txLive tx 1`;
- walk or open a bucket of the same transaction (`rtxStats` is the walk's): harmless in Go
  (`TestNestedReadWalkWorks`), excluded conservatively. -/
abbrev bbolt.Bucket.ForEach_kvr.spec : Prop :=
  ∀ (tx b : Loc) (q : Qp) (es : List Ent) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rBkt tx b es ∗ rtxStats tx ∗ txLive tx q ∗
      I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜es[i]? = some e⌝ →
          {{ I i ∗ txLive tx q.half ∗ ⌜k ≠ slice.nil⌝ ∗ txBytes tx k e.1 ∗ txBytes tx v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive tx q.half ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; rtxStats tx ∗ txLive tx q ∗
      ((⌜err = GoInterface.nil⌝ ∗ I es.length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < es.length⌝ ∗ E i err)) }}

end spec

end EtcdGrove
end Perennial
