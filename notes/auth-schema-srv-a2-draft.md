# auth-schema-srv A2: `UnsafeForEach` — the trust boundary (Draft, 2026-11-17)

**Decided (2026-11-17, the user via etcd-grove-03): (B).** The texts are
`Spec/go_etcd_io/bbolt/Bucket__ForEach_kvr.lean` and `Bucket__ForEach_kvw.lean` (each docstring says why it is
faithful), backed by `examples/bbolt/foreachkv/foreach_test.go`; awaiting the independent attack before the
axioms (`Proof/go_etcd_io/bbolt/Bucket__ForEach_kv{r,w}.lean`) are added and used. Design points: the visitor
gets half of the walk's `txLive` (a visitor with all of it could meet `Tx.Rollback_kv` and close the read
transaction mid-walk: `TestVisitorRollbackPanics`); the walk keeps `rtxStats` (kvr) and `ownWTxG` (kvw), so the
visitor can neither walk the transaction again (conservative) nor write the bucket (`TestVisitorDeleteSkips`,
`TestVisitorPutVisited`).

Scope §3 A2, Q7 (decided by etcd-grove-02): "one bbolt kv axiom `Cursor.First_kv` (the twin of `Seek_kv`), and
bbolt's `Bucket.ForEach` proved over it". This Draft gives that axiom's text and reports a gap in the plan:
`Bucket.ForEach` cannot be proved over the kv contract with `First_kv` alone.

## 1. `Cursor.First_kv` (the planned axiom)

Go (bbolt v1.5.0, `cursor.go:32-42`): "First moves the cursor to the first item in the bucket and returns its key
and value. If the bucket is empty then a nil key and value are returned. The returned key and value are only
valid for the life of the transaction." `common.Assert(c.bucket.tx.db != nil, "tx closed")`: excluded by
`txLive`. A nested bucket's entry returns `v = nil` (`BucketLeafFlag`): excluded as for `Seek_kv` (the backend's
buckets hold no nested bucket; `Ent`s are key-value pairs).

```lean
/-- `c.First()`: the first entry (nil, nil in an empty bucket). -/
abbrev bbolt.Cursor.First_kv.spec : Prop :=
  ∀ (tx c : Loc) (es : List Ent) (pos : Option Nat) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownCur tx c es pos ∗ txLive tx q }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"First")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); ownCur tx c es (some 0) ∗ txLive tx q ∗ curAt tx es 0 k v }}
```

It is `Seek_kv` at the empty key (`seekIdx es "" = 0`) without the key slice.

## 2. The gap: `Bucket.ForEach` reads `b.tx.db`

```go
func (b *Bucket) ForEach(fn func(k, v []byte) error) error {   // bucket.go:585
	if b.tx.db == nil {
		return errors.ErrTxClosed
	}
	c := b.Cursor()
	for k, v := c.First(); k != nil; k, v = c.Next() {
		if err := fn(k, v); err != nil {
			return err
		}
	}
	return nil
}
```

The translation (`Code/go_etcd_io/bbolt.lean`, `Bucket.ForEach.impl`) loads the fields `b.tx` and `tx.db`. The
kv contract's bucket and transaction predicates (`rBkt`, `wBkt`, `txLive`, `ownWTxG`: `InvBbolt.lean`) are
opaque axioms that give no points-to of bbolt's memory, so a proof of `ForEach` over `Cursor_kv{r,w}`,
`First_kv` and `Next_kv` has no way to take that first branch. Every other kv axiom is on a translated method
whose body reads bbolt's internals the same way (`Bucket.Cursor` reads `b.tx`, `Cursor.Seek` asserts on
`tx.db`); `ForEach` is the first one planned as a proof.

## 3. Options

- **(A) `First_kv` plus a field law.** One more axiom: under `txLive tx q`, a fraction of `tx.db`'s field, not
  nil, and under `rBkt tx b es`/`wBkt tx b n g` the field `b.tx = tx` (read-only: a `Bucket`'s `tx` never changes).
  Trust: 1 method axiom + 1-2 laws on bbolt's memory, which every kv axiom that closes the transaction (`Commit`,
  `Rollback`: `tx.db = nil`) must then respect (they consume `txLive` whole: true today, but a new constraint on
  the opaque predicates). `ForEach` then proved for both the read and the write transaction.
- **(B) `Bucket.ForEach_kv{r,w}` axioms** (recommended), mirroring `Bucket.Cursor_kv{r,w}`: no `First_kv`. A
  higher-order spec: for an invariant `I : Nat → IProp` and an error resource `E`, a visitor spec "for the `i`-th
  entry `e`, from `I i ∗ txLive tx q` with the key and value `txBytes` of `e`, `fn k v` returns nil with `I (i+1)`,
  or an error with `E i err`" gives `I es.length` (nil) or `E i err` (the first error). Trust: 2 method axioms,
  nothing on bbolt's memory; the kvw one holds the transaction's ownership during the walk (as `Cursor_kvw`, whose
  cursor reads the materialized nodes) and passes the visitor only `txLive`, so the visitor cannot write the
  bucket (Go: "undefined behavior").
- **(C)** prove `ForEach` in the bbolt proof's own model (`Proof/go_etcd_io/bbolt`, real pages): not linkable to
  the kv contract the backend uses; out of scope.

Recommendation: (B). Every kv axiom is a method spec of the documented behaviour; (A) would put the first
memory fact about bbolt's internals into the kv contract to save one axiom.

## 4. After the decision

The backend side, proved (no trust change): `unsafeForEach` (`tx.Bucket(name)`, nil → nil, else `ForEach`),
`batchTx.UnsafeForEach` (write transaction: the session's view `st.S`'s bucket, as `UnsafeRange`'s
`unsafeRange` over `Seek_kv`), `baseReadTx.UnsafeForEach` (the read buffer's `ForEach` for the duplicates, a
`map[string]struct{}`, `unsafeForEach` over bbolt under `txMu`, then the buffer's `ForEach`: the visitor sees
the merged contents `rvBkt`, each key once, bbolt's keys not in the buffer in order then the buffer's). The
specs follow `UnsafeRange`'s (`batchTxBuffered.UnsafeRange`, `readTx.UnsafeRange`) with the visitor's invariant.
