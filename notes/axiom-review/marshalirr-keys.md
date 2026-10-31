# Axiom review: `proto.MarshalIRR`'s key-length conjunct (`irrKeysLe`)

- **Axiom**: `proto.MarshalIRR.wp_proof` (`Proof/google_golang_org/protobuf/proto/MarshalIRR.lean`),
  its spec `proto.MarshalIRR.spec` (`Spec/google_golang_org/protobuf/proto/MarshalIRR.lean`) as
  strengthened by `0d43bc2dd8` (branch `invoke-size`): the success branch's pure fact gains
  `apply.irrKeysLe bs.length rq'` (`apply/InvRequest.lean`: the decoded request's `Put` key, and
  every put key of its transaction at any depth, through `TxnOpW.toOp`/`putTxnOp`, is at most
  `bs.length` bytes). Only the new conjunct is under review; the rest of the triple was reviewed
  before (`notes/audit.md`; the depth finding below).
- **Intent** (`notes/keylen.md`, `notes/decisions.md` "The key-length law"):
  `processInternalRaftRequestOnce` (`server/etcdserver/v3_server.go:1094-1114` at the pin) marshals
  the request, refuses `len(data) > int(Cfg.MaxRequestBytes)`, and proposes `data` itself; with
  `NewServer`'s scope premise `etcdMaxRequestBytesOk` this bounds every put key by `etcdKeyMax`.
- **Revision**: etcd fork `goose-lean` as in `.lake/go-src/etcd`; protobuf-go v1.36.12; go1.27.3.
- **Verdict: survives** (2026-10-31). No counterexample; none built (no Goose project, no Lean).

## Why it is true

The conjunct is a fact of the *decoder*, not of the encoder: it is stated of `rq'` with
`irrDecode bs = some rq'`. A protobuf `bytes` field's value, whenever decoding succeeds, is the
payload of one length-delimited record of the input (the last one, for a singular field), and a
nested message's fields are read from a sub-range of its parent's payload; so every key of any
successful decoding of `bs` is a contiguous sub-range of `bs`. `irrDecode`'s model of a put's key is
the `Key` bytes unchanged (`putOpOf`, `putTxnOp`: `.put/.putKeep/.putIgnVal o.key ...`). The
only other statement about `irrDecode` (`pbutil.MustUnmarshalMessage.spec`) uses it as a premise and
says nothing of keys, so the conjunct cannot conflict with another axiom.

Checked in Go (scratch test, not committed; protobuf-go v1.36.12, the pinned `etcdserverpb`): a
1 MiB `Put` key (`len(bs)=1048589`), a put 60 transactions deep (`1049072`), and 200 000 mutated
encodings (duplicated, byte-flipped, byte-inserted) of which 107 566 decode: no decoded put key,
at any depth, is longer than the input.

## Attacks tried

1. **Field-encoding overhead; can a key exceed the encoding?** No: tag and varint length are extra
   bytes; the key is copied whole. A set-but-empty key is omitted (length 0). A non-nil empty
   `Put`/`RequestOp` is still emitted (tag, 0) and decodes to a key `[]`. Bound holds with slack
   (13 bytes for a top-level put).
2. **Keys reaching the state other than through a put's key.** Range-end deletes, lease revoke
   (`lessor` → `LeaseRevoke` → `raftRequestOnce`, the same marshal-and-check path), compaction and
   the delete side of a txn only remove keys; lease attach is a put's lease on its own key; auth's
   users and roles are bbolt keys of other buckets, not `etcdState`'s KV; the server creates no KV
   key itself. `v3_server.go:1114` is the only `Propose` in `server/etcdserver` (conf changes go
   through `ProposeConfChange`, raft's own empty entries have no data). `putIgnVal` on an absent key
   fails the transaction. The start log is `[[], []]` (`NewServer`). Nothing escapes `irrKeysLe`'s
   two clauses (`rq.put`, `rq.txn`); a request with both `Put` and `Txn` set has both bounded.
3. **Nested transactions.** `TxnOp.putKeysLe` recurses through both branches at every depth; each
   level's payload is a sub-range of its parent's, so the bound needs nothing shared. Tested at 60.
4. **Is `bs` the bytes checked against `MaxRequestBytes`?** Yes: `data, err = proto.Marshal(r)`
   (line 1094, after `r.Header` is set), `len(data) > int(s.Cfg.MaxRequestBytes)` (1099),
   `s.r.Propose(cctx, data)` (1114): one slice, no later encoding. The proof (`invoke-size`,
   `EtcdServer__processInternalRaftRequestOnce.lean`, `Hk`) uses the conjunct with the `bs` of the
   same success branch whose length the `if` bounds. `int(...)` of a huge `uint` is excluded by
   the scope premise.
5. **unknownFields.** `proto.Marshal` emits a message's unknown fields raw after its known ones.
   Set by `SetUnknown` to a known field's encoding (outer field 4 holding a `PutRequest` with a
   1 MiB key while `r.Put.Key = "a"`; or `PutRequest` field 1 re-set), the decoded key is the
   unknown bytes' (1 MiB), still within `bs` (`1048589`): the conjunct holds because it is stated of
   `rq'`. (A side observation on the *other* conjunct: there `rq' ≠ rq` although `irrNoZeroEnd rq`,
   so `irrWireOf` is false of such a message. Not reachable: no etcd server code calls
   `SetUnknown` or `proto.Merge` on a request, unknown fields come only from decoding, where they
   hold unknown field numbers or a known number with the wrong wire type, which stays unknown
   through the round trip (tested: field 1 as a varint); and the API is names-only, so no
   translated program reaches it. Recorded, no finding.)
6. **Interaction with the depth finding** (`issues/etcd-txn-nested-depth-apply-panic.md`, branch
   `axiom/txn-nested-wire`: `irrDecode bs = some rq'` is false of a request more than 10 000
   messages deep). The new conjunct is independently sound: it is true of every successful
   decoding, so it adds no falsehood, and any restatement that makes the decoding conditional (a
   depth bound, or "decodes or the entry poisons the log") keeps it as is under the same condition.
   It does not repair or worsen the depth falsehood.

## Not tried / scope

- Other members' configuration: the bound on committed entries rests on every proposing member's
  `MaxRequestBytes` meeting `etcdMaxRequestBytesOk`; a member configured beyond it (etcd only warns
  above 10 MiB) is outside the scope restriction, not an axiom question.
- A backend restored from a snapshot or data directory written under a larger limit: outside the
  model (the start log is empty).
- No Lean counterexample was attempted: no Go program falsifies the conjunct.

## Proposed restatement

None needed. Optionally, since it is a decoder fact, it could live beside `irrDecode` as
`irrDecode bs = some rq → irrKeysLe bs.length rq` (true of every input, and independent of
`MarshalIRR`'s depth repair); that would be a new axiom, so not proposed for now.
