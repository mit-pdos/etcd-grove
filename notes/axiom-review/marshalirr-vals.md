# Axiom review: `proto.MarshalIRR`'s put-length conjunct, extended to values (`irrPutsLe`)

- **Axiom**: `proto.MarshalIRR.wp_proof` (`Proof/google_golang_org/protobuf/proto/MarshalIRR.lean`),
  its spec as changed by `f5c9aceb9a` (branch `invoke-size`): the success branch's pure fact states
  `apply.irrPutsLe bs.length rq'` in place of `irrKeysLe` (vocabulary `769ff90213`:
  `apply.irrPutsLe`, `TxnOp.putsLe`/`opsPutsLe`, `TxnModel.putsLe`). `irrPutsLe n rq`: the
  `Put`'s key **and value** (`o.val`, whatever `IgnoreValue` says), and every transaction put at
  any depth through `TxnOpW.toOp`/`putTxnOp`: `.put k v _`, `.putKeep k v` key and value,
  `.putIgnVal k _` key only.
- **Intent**: `notes/vallen.md`, `notes/decisions.md` "The value-length law" (the state's values
  at most `etcdKeyMax`, from the same `MaxRequestBytes` check as the keys).
- **Earlier review**: the keys' conjunct (`0d43bc2dd8`) survived,
  `notes/axiom-review/marshalirr-keys.md`; its
  attacks on the keys (encoding overhead, other paths, `bs` = the checked and proposed slice,
  unknown fields, the depth finding) carry over and are not repeated here.
- **Revision**: the etcd fork as in `.lake/go-src/etcd`; protobuf-go v1.36.12; go1.27.3.
- **Verdict: survives** (2026-10-31). No counterexample; none built.

## Why it is true

As for the keys, a fact of every successful decoding: `PutRequest.Value` (field 2) is a `bytes`
field, so a decoded value is the payload of one length-delimited record inside `bs`, at every
depth. `putRequestIs` maps the Go `Value` bytes to `o.val` unchanged (`putOpOf k v ...`,
`txn/Requests.lean`). `irrPutsLe` bounds nothing that is not such a field.

Go (scratch test `vals_test.go` beside the keys' harness, not committed): a 1 MiB value with a
lease and `PrevKv` (`len(bs)=1048591`), the same with `IgnoreValue` and `IgnoreLease`, an empty
value, a put 60 transactions deep under levels that each carry a 1 MiB compare value
(`len(bs)=63964416`), a value re-set through the `PutRequest`'s unknown fields (`1048590`), and
200 000 mutated encodings (112 124 decodable): no decoded key or value of any put, counting the
value field even under `IgnoreValue`, is longer than the input.

## Attacks tried

1. **`IgnoreValue`.** The conjunct is about the request's `Value` field only: at the top level it
   bounds `o.val` whether or not `ignoreValue` is set (true: the field is decoded bytes; gRPC also
   refuses `IgnoreValue` with a non-empty value, `v3rpc/key.go:186`, but the conjunct does not need
   it); in a transaction `putTxnOp` makes it `.putIgnVal`, which `putsLe` bounds by its key only
   (weaker, so no stronger claim to break). The value stored by such a put is the old one
   (`txn/put.go:54`), not bounded by this conjunct: that is the downstream proof's job, which
   `notes/vallen.md` says it does (`srvOp_keys`/`srvOps_keys` take the state's values' bound, an
   induction on the state). Not an axiom question.
2. **Lease, `PrevKv`, compare values.** A lease is a `int64` and `PrevKv` a `bool`: neither is
   bounded nor needs to be. A `Compare`'s value (`TargetUnion` `Value`) is not counted by
   `putsLe` (`.txn _ ts es` ignores the comparisons), and should not be: a comparison writes
   nothing to the state. Counting it would also be true (a bytes field), but unneeded.
3. **Values entering the state not through a decoded put.** None: lease grant/revoke/checkpoint
   (the lessor's buckets; revoke deletes keys), auth (users, roles, passwords: the auth buckets),
   alarms (the alarm bucket), cluster version, member attributes and downgrade (the meta/cluster
   buckets) write no KV value; compaction and deletes only remove. The only writers of a KV value
   are `put` at the top level and in a transaction, both bounded (or, for `IgnoreValue`, a copy of
   a value already in the state, attack 1). The start log is empty (`NewServer`).
4. **Nested depth and empty values.** `opsPutsLe` recurses through both branches at every depth;
   tested at 60 levels. An empty value is not emitted and decodes to `[]` (length 0). The depth
   finding (`issues/etcd-txn-nested-depth-apply-panic.md`: `irrDecode bs = some rq'` false above
   10 000 messages) is independent: the conjunct holds of every successful decoding, so a
   restatement that makes the decoding conditional keeps it unchanged.

## Not tried / scope

The same as the keys': members configured beyond `etcdMaxRequestBytesOk`, a backend restored from
data written under a larger limit, a Lean counterexample (no Go program falsifies the conjunct).

## Proposed restatement

None needed (optionally, as for the keys, a decoder fact `irrDecode bs = some rq → irrPutsLe
bs.length rq`, which would be a new axiom; not proposed).
