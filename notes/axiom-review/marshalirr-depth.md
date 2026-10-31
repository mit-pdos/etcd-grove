# Axiom review: `proto.MarshalIRR` restated with the depth premise (`apply.irrDepthOk`)

- **Axiom**: `proto.MarshalIRR.wp_proof` (`Proof/google_golang_org/protobuf/proto/MarshalIRR.lean`),
  its spec as restated on branch `irr-depth` (`Spec/google_golang_org/protobuf/proto/MarshalIRR.lean`):
  the new premise `apply.irrDepthOk rq →`, the post unchanged. The vocabulary
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/IrrDepth.lean`): `apply.irrDepthOk rq := ∀ t,
  rq.txn = some t → apply.txnDepthOk t`, `apply.txnDepthOk t := t.msgDepth + 1 ≤ 10000`,
  `TxnModel.msgDepth t = 1 + max [t.cmps ≠ []] (deepest operation of either branch)`,
  `TxnOp.msgDepth (.txn cs ts es) = 2 + max [cs ≠ []] (deepest of ts, es)`, `2` for a get, a put
  (every `putTxnOp` form), a delete.
- **Intent**: `notes/irr-depth.md`; `notes/decisions.md`, "A depth premise for `proto.MarshalIRR`".
  The defect repaired: `axiom/txn-nested-wire`'s attack 9 (`notes/axiom-review/txn-nested-wire.md`
  on that branch), `issues/etcd-txn-nested-depth-apply-panic.md`.
- **Earlier reviews of the same axiom**: the key and value conjuncts survived
  (`marshalirr-keys.md`, `marshalirr-vals.md`); their attacks (encoding overhead, other paths, `bs`
  the checked and proposed slice) are about the post, unchanged here, and are not repeated.
- **Revision**: the etcd fork `249d76bea7` (`.lake/go-src/etcd`); protobuf-go v1.36.12; go1.27.3.
- **Verdict: survives** (2026-10-31). No counterexample; none built.

## Why it is true

The restatement claims the old post only of requests whose every message is at most 10000 levels
deep, the top one counted; for those protobuf-go's decoder has no other failure the old reviews did
not cover. At the pin:

- `proto.Unmarshal` (`pbutil.MustUnmarshalMessage`'s, `pkg/pbutil/pbutil.go`) is
  `UnmarshalOptions{RecursionLimit: protowire.DefaultRecursionLimit}` (`proto/decode.go:61-63`),
  `DefaultRecursionLimit = 10000`; `MessageInfo.unmarshalPointer` decrements the count on entry to
  every message and fails below 0 (`internal/impl/decode.go:105`), nested message fields passing
  the decremented count down. So the bytes decode (as far as depth goes) iff every message is at
  level `≤ 10000`.
- The only recursion of `InternalRaftRequest` (`api/etcdserverpb/raft_internal.proto`) is its `Txn`
  (`TxnRequest` → `RequestOp` → `TxnRequest` …); every other field is at most two levels below it
  (`AuthUserAddRequest.Options`, `AuthRoleGrantPermissionRequest.Perm`,
  `LeaseCheckpointRequest.Checkpoints`, `ClusterMemberAttrSetRequest.MemberAttributes`), so without a
  transaction the request is at most 3 deep (the premise's vacuous case), and with one its depth is
  the transaction's plus one.
- `internalRaftRequestIs` owns every one of the 32 fields, and `txnRequestIsW` every field of the
  transaction's messages; `TxnModelW.toModel` keeps the tree (`TxnOpW.toOp`, `toOps`), so the model's
  `msgDepth` is the heap's path depth.

## Go checks (scratch module, not committed)

A test module beside the fork's `api` (`depthcheck`, `go test` at go1.27.3, protobuf-go v1.36.12),
with `TxnModel.msgDepth`/`TxnOp.msgDepth` transcribed to Go over `*pb.TxnRequest`:

- `TestDepthExact`: chains nested 4995 to 5001 times over four innermost shapes (an empty
  `TxnRequest`, one with a comparison only, one with a put, one with a delete in `Failure`), nested
  in `Success` (with a sibling get in `Failure`) or in `Failure`, each alone in the request and with
  every other of the 32 fields set at its deepest: 48 requests at model depths 9997 to 10002. For
  each, `proto.Unmarshal(proto.Marshal(rq))` succeeds iff `msgDepth + 1 ≤ 10000`: the premise is
  exact, neither too strong (no decodable request excluded) nor too weak.
- `TestNoTxnShallow`: the request with every field but `Txn` set decodes.
- `TestSharedOps`: a DAG (one `RequestOp` referenced at every level and twice per level) at depths
  9999 and 10001 decodes iff the tree model's depth says so.
- `TestUnknownFields`: a `TxnRequest` decoded from bytes carrying unknown fields of 1 to 10001
  nested groups (as gRPC's decoding leaves them), nested 4000 deep in an `InternalRaftRequest`,
  re-encodes and decodes: unknown groups are skipped against a fresh limit
  (`protowire.ConsumeFieldValue`, `encoding/protowire/wire.go:112-113`), wherever they sit.

## Attacks tried

1. **The boundary itself** (an off-by-one in `msgDepth`, the `+ 1` for the request, the comparisons'
   level, the empty transaction's): `TestDepthExact`, both sides of the limit, every bottom shape.
   Exact.
2. **A field other than `Txn` adding depth**: none is recursive; the deepest is 2 below the request
   (the proto file); with a transaction at the limit and every other field set, the request still
   decodes (`TestDepthExact`, `withAll`).
3. **Sharing and cycles in the heap**: a shared `RequestOp` is encoded at each reference
   (`TestSharedOps`); the tree model unfolds it the same way. A cycle cannot satisfy the predicates:
   `txnRequestIsW` relates a location's read-only contents to a finite model, structurally, so a
   cycle would make a model its own strict subterm.
4. **Unknown fields** (outside the model: `internalRaftRequestIs` does not own `unknownFields`): Go
   code outside protobuf can set them only by reflection (`ProtoReflect().SetUnknown`, no spec) or
   by decoding (gRPC's handler, `proto.Unmarshal`), which keeps only bytes it parsed; their groups
   count against a fresh limit at both decodings (`TestUnknownFields`). Not a gap reachable by a
   program with a proof; recorded as a margin (the size caches, also outside the model, are the
   header's).
5. **Lazy decoding, `required` fields, proto2 groups as fields**: the request's messages have none
   (`raft_internal.proto`, `rpc.proto`, `auth.proto`, `membership.proto` are proto3, generated by
   `protoc-gen-go` v1.36.12; no `[lazy = true]`; the proto2 `etcdserver.proto` is the v2 request,
   the reserved field 2).
6. **Marshalling at depth**: `proto.Marshal` has no depth check and recurses once per level; at
   depths the premise admits (≤ 10000) it returns (the tests marshal every case). The premise
   claims nothing of deeper requests, where the old axiom claimed decodable bytes (false) and a
   weakened post would have claimed that `Marshal` returns (Go's 1 GB stack limit: a fatal error
   past it).
7. **A premise too strong for the callers**: the server's proofs discharge it (the proposer passes
   it on; `Put`, `DeleteRange`, the admin and `Authenticate` requests have no transaction; a writing
   `Txn` takes `txnDepthOk`, which the gRPC handler proves from `checkTxnRequest` at a budget within
   `maxTxnOpsOk`, `v3rpc.txnCheck_msgDepth`). A premise that excluded a request the code applies
   safely would be a completeness defect, not a soundness one; attack 1 shows none is excluded.

## Not tried / scope

A Lean counterexample (no Go program falsifies the restatement). Members configured with
`--max-txn-ops` above 4999: outside the proof's scope (`NewServer`'s premise
`v3rpc.maxTxnOpsOk`), where the issue's panic is real. Entries written by another etcd version
(the WAL replayed from a member without the premise): out of scope, as for the other conjuncts.

## Proposed restatement

None needed.
