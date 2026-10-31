# etcd-txn-keysonly-reply-alloc-panic

## Security classification: for the user to decide before anything is public

Decision pending (the user's); the upstream route is on hold: nothing filed, pushed or commented. A public filing
(issue, PR, or the fix branch pushed to `upamanyus/etcd`) would expose that one `Txn` from any client that can send
one (with auth enabled, a user with permission on the keys it reads) can crash the member serving it on `main`
(with `--max-request-bytes` of about 10 MiB or more and a long enough request timeout), and that on every branch it
makes every member build a reply of many GiB, because nested transactions bypass `--max-txn-ops`. The PR's title and
test alone already reveal the bypass.

Options:
1. A private report through the GitHub security advisory form
   (https://github.com/etcd-io/etcd/security/advisories/new, per `security/README.md`): `issue.md` is drafted as
   its text (Summary, Details, PoC, Impact); the fix goes in the advisory's temporary private fork, not on
   `upamanyus/etcd`; `pr.md` is for after disclosure.
2. A public issue and PR. etcd's `THREAT_MODEL.md` (2026-07) says crashes and memory exhaustion triggered by an
   authenticated client are robustness defects, not vulnerabilities, and that reports predicated on a non-default
   flag are configuration hardening; a report outside it is "welcome through normal issues and pull requests". By
   that text this finding is most likely a robustness defect (the client is inside the mTLS perimeter; the crash
   needs a non-default `--max-request-bytes`), and the PSC may redirect a private report to the public route. The
   public route would then rewrite `issue.md` into the bug-report form (as `example/issue.md`) and push the branch.
3. Leaving it.

## Candidate

- **Finding**: `issues/etcd-txn-keysonly-reply-alloc-panic.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-txn-keysonly-reply-alloc-panic` in `/shared/etcd-fixes/etcd-txn-keysonly-reply-alloc-panic` (a worktree of the shared fork clone `/shared/etcd`, `origin` upamanyus/etcd over SSH), two
  commits (signed off, no trailers): 511703d7b (`etcdserver: test the operation limit of nested txns`) adds the
  tests; 7a63f2b96 (`etcdserver: count nested txns' operations toward --max-txn-ops`) is the fix. Not pushed (push: `git -C /shared/etcd-fixes/etcd-txn-keysonly-reply-alloc-panic push origin fix/etcd-txn-keysonly-reply-alloc-panic`).
- **Base**: upstream `main` 1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28).
- **State**: draft (security decision pending)
- **Upstream issue**: —
- **PR**: —

## Re-check at the base and on the release branches

At 1573d5941, unchanged from the finding (the fork's 249d76bea, which differs from main on this path only by two
unrelated fixes in `checkIntervals` and `rangeStream`): `checkTxnRequest`'s per-level budget (`maxTxnOps-opc`,
`key.go:202-231`, from 6ed51dc62, "support nested txns", 2017); keys-only ranges returning the index's key slices
(`treeIndex.Range`, `index.go:162-187`; the `FastKeysOnly` branch of `rangeKeys`, `kvstore_txn.go:88-106`, added by
7624a8a2e on 2026-05-20); `IsTxnReadonly` inspecting the top level only (`txn/txn.go:352-364`); the codec
(`codec.go`, `proto.Marshal`), with grpc v1.84.0, protobuf-go v1.36.12, golang/protobuf v1.5.4, send limit
`math.MaxInt32` (`grpc.go:36,75`).

Release branches (read only, nothing run): `release-3.6`, `release-3.5` and `release-3.4` have the same per-level
budget and a top-level-only read-only check, but no `FastKeysOnly`: keys-only ranges unmarshal (copy) each key
from the backend. There the reply's heap equals its encoded size, so the 2^48 panic is out of reach, but the
op-limit bypass still lets one request make every member build a reply of (leaves × keyspace) bytes: an
out-of-memory, by code reading, not reproduced.

## Duplicates checked (2026-10-31)

Five unauthenticated searches of etcd-io/etcd issues and PRs (GitHub search API): `nested txn max-txn-ops` (0),
`nested txn maxTxnOps` (0), `makeslice cap out of range` (0), `txn response too large panic` (11, none related:
#14211, #14370, #12535 and others about consistency and tests; #9826 adds response size to a slow-request
warning), `keys-only range OOM` (3: #21834, `FastKeysOnly` limit support, merged; #11990, the index-limit
push-down; #12290, a QoS proof of concept; none about the op limit or this panic). No duplicate; no open PR fixes it.

## Verification (go1.27.3 linux/amd64, `GOFLAGS=-p=4`)

| code | command | result |
|---|---|---|
| base 1573d5941 | `go test ./etcdserver/api/v3rpc/` (server) | ok |
| base | `go test ./integration/ -run TestV3Txn` (tests) | ok |
| tests commit 511703d7b | `go test ./etcdserver/...` (server) | only `TestCheckTxnRequestNestedOps` fails: `expected "...too many operations in txn request", but got ""` |
| tests commit | `go test ./integration/ -run 'Txn\|Auth\|KV\|Put\|Range'`; `./integration/clientv3/ ./integration/clientv3/lease/ -run 'Txn\|KV\|Leasing'` | only `TestV3TxnNestedTooManyOps` fails: `err = <nil>, want ...too many operations in txn request`; the rest ok |
| fix 7a63f2b96 | the same three commands | all ok |

`gofmt -l` empty; `go vet ./etcdserver/api/v3rpc/` (server) and `./integration/` (tests) clean. The leasing tests
are included because the leasing KV sends nested txns.

The full crash reproduction (`examples/etcdbugs/keysonlyreply/repro_test.go`, 12.8 GiB peak RSS) was run on
2026-10-31 at the fork's 249d76bea (same code on this path as the base), not rerun at the base or the fix. With the
fix its request (2,560,000 leaf ranges, fan-outs summing to 96) is rejected by `checkTxnRequest` before it is
proposed (by code reading: its operation count is far above 128).

`check.py` (2026-10-31): the commit and PR checks pass (two commits, tests first, signed off, no trailers, gofmt
clean, PR title = fix subject). Two FAILs come from the advisory shape and are kept while the route is private: no
link to the test on `upamanyus/etcd` (a private report must not point at a public branch; the test is inline) and no
"Anything else we need to know?" section (the advisory form's sections instead). WARNs kept: the doc comment of the
new `txnOps` (Go convention for a new function); the issue at 487 words and naming `checkTxnRequest` (an advisory
carries details and code names; if the public route is chosen, the issue is rewritten in the bug-report form
without them).

Not run: the whole `tests/integration` suite, `tests/e2e`, `make verify`, release branches.

## Why the tests show the bug and not a misuse

The request is an ordinary `Txn` built with the public API (`clientv3.OpTxn` nests, `WithKeysOnly`,
`WithFromKey`). `--max-txn-ops` is documented as "Maximum number of operations permitted in a transaction"; a
request of 4096 range operations under a limit of 128 contradicts it. The tests assert only the rejection.

## Why the fix works

At the base, `checkTxnRequest` computes the level's count `opc = max(len(Compare), len(Success), len(Failure))`
and checks each nested txn against `maxTxnOps - opc`. That bounds every root-to-leaf path's sum of counts, but
sibling nested txns each get the whole remaining budget, so the number of operations is the product of the
fan-outs. With the fix, `txnOps` sums the level counts over the whole tree (both branches, conservatively, since
only one runs) and `checkTxnRequest` rejects a request whose sum exceeds the limit. Every request the base rejects is
still rejected (a path's sum is at most the tree's), and a request with at most one nested txn per txn gets the
same answer as before. The nested calls of `checkTxnRequest` keep the limit (their own sums are smaller, so the
count check there always passes; the rest of the validation is unchanged). `txnOps` walks the request once,
linear in its size, before anything else.

After the fix, a txn has at most `--max-txn-ops` ranges, so its reply is at most (max-txn-ops × the keyspace's
encoded size): 128 × 8 GiB = 2^40 bytes, far below the 2^48 at which the codec's allocation panics. Every variant of
the panic goes through this check: nested txns (closed), flat read-only txns (already at most 128 ranges), write
txns (the same check).

## If a reviewer asks

Candidate fixes, and why this one:
- **Copy keys in the keys-only branch** (`rangeKeys`): removes the aliasing, so the reply's heap equals its encoded
  size; the same request then exhausts memory on every member instead of panicking on one. It costs a copy on every
  keys-only range (the optimization 7624a8a2e added) and does not bound anything. Rejected.
- **Bound the total operations of a nested txn** (this fix): the root cause is that the documented limit is not
  enforced; the change is a few lines in the check that already exists, at the gRPC boundary every client request
  passes. Behavior change: a nested txn whose operations sum over siblings beyond `--max-txn-ops` is now rejected
  with `ErrGRPCTooManyOps` (raise the flag if needed). Nested txns are rare (Kubernetes does not use them); the
  leasing KV's are a few operations.
- **Check the reply's size before marshalling** (e.g. `proto.Size` against the send limit in `kvServer.Txn`, or in
  etcd's codec): would turn a too-large reply into `ResourceExhausted`, but only after every member built it
  (12.8 GiB here), adds a second size walk of every reply on the hot path, and leaves the op-limit bypass and its
  apply-time cost. A reasonable separate hardening (it would also avoid allocating up to the reply's size for a flat
  reply above 2 GiB that grpc then rejects); not in this PR. The allocation before the size check is grpc-go's /
  protobuf-go's (the same root cause as this repository's `grpc-codec-alloc-before-size-check`).
- **Make `IsTxnReadonly` recursive**: a nested all-read txn would be served without raft, so it would not be in the
  WAL nor applied on every member; it bounds nothing and the panic remains. Separate (a performance and WAL-hygiene
  change), not in this PR.

What the fix does not cover: a flat txn of 128 whole-keyspace ranges still builds a reply of 128 × the keyspace (on
`main`, for keys-only ranges, small in heap but allocated in full by the codec; elsewhere, in heap). That is the
general cost of large reads, as on the release branches, not a bypass of a limit; the reply-size check above would
address its keys-only part.

- Backports: the bypass exists on release-3.4/3.5/3.6 (above); the fix's code applies there (the function is the
  same); not tried.

## Applying the same fix elsewhere

In `server/etcdserver/api/v3rpc/key.go` (`etcdserver/api/v3rpc/key.go` on 3.4): in `checkTxnRequest`, replace the
`opc` computation and check by `if txnOps(r) > maxTxnOps { return rpctypes.ErrGRPCTooManyOps }`, pass `maxTxnOps`
(not `maxTxnOps-opc`) to `checkRequestOp`, and add `txnOps` (on Go before 1.21, without the built-in `max`).
