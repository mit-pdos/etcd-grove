# Brief: repairs after the verification round (2026-11-09)

The verification round (`verify-brief.md`) ran 22 independent reviews (provability and
completeness per area); the reports are in `notes/specs-only/verify/`. Most batches FAILed on
specific first-tier findings. You repair one **group**: the files your prompt says you own.

Read first: `notes/specs-only/README.md`, `.claude/skills/spec/PRINCIPLES.md`, then the verify
reports your prompt names (both kinds), in full. Worktree:
`/home/ubuntu/etcd-grove/.claude/worktrees/specs-only`; Go sources `.lake/src/{client,server,api,
pkg,cache,raft,bbolt}`.

## What to do

1. **Every first-tier finding** in your reports that touches files you own: fix it in the spec
   (a premise, a post, a missing law or spec, a trust-boundary spec stated as assumed, a corrected
   snippet or a new one). Fix the second-tier items too when the fix is cheap and local. The
   reviewer's suggested fix is a suggestion: make the spec right (sound, complete, local, no
   unneeded premise), and say if you chose differently and why.
2. Keep the conventions: every obligation is a `def … .spec : Prop` (no `axiom`, `theorem`,
   `sorry`, `instance` of a law); opaque predicates carry their heap binders explicitly
   (`[GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]`
   on an IProp-valued `opaque`); update each changed spec's Proof sketch / Users / Changes block
   comments (a `Changes:` line `verify-round: …`).
3. **Sentinel error values** (cross-cutting, A3-provability F4): a package's `var ErrX =
   errors.New(...)` cannot be equated with a fixed Lean constant (`errors.New` returns a fresh
   pointer). Use the encoding the cache batch uses: the package's init law gives the global's
   value existentially (`globalAddr ErrX ↦□ e`, the values pairwise distinct and non-nil), and a
   spec's post that returns that error returns the value read from the global. Check your own
   packages' error vocabularies (`srvErrVal`, `vErr`, `ErrLocked`, ... whatever yours are) and fix
   them.
4. **Snippets** (`examples/specreq/<pkg>/`): fix those the reports found unprovable; keep them
   `go vet`-clean (`cd examples && go vet ./specreq/<pkg>/...`).
5. **Findings in the Go code** (a reviewer's possible bug): file it per `issues/README.md` (in
   `nonissues/` unless you have a failing Go test reaching it the way etcd uses the code).
6. **Build** what you changed: `etc/specs-build.sh --dir <your Spec dir>` (serialized by a lock;
   other groups build too, so it may wait). Your files must build before you finish.

## Ownership

Edit only files you own (Spec files, snippet packages, your report). Another group's file: write
the request in your report under **Requests to <group>** (the file, the exact change, why); the
coordinator routes it. Do not edit `open-questions.md`, `batches.md`, `STATUS.md`, `top.md`. Do not
run git commands that change the repository (no commit, stash, checkout, reset).

Groups: `client-core` (client/v3 except watch files; api/v3 Model/State/Wire; client/pkg,
credentials, internal, kubernetes; zap, context, otel, fmt), `client-watch` (client/v3 `watch*`,
`Watch*`, `ApiWatch`, `streamKeyFromCtx`, `progressRequest`, `watchRequest`, `OpWatch` files),
`client-users` (concurrency, recipes, leasing, cache, btree), `raft-core` (raft/v3 top-level),
`raft-conf-pb` (raft/v3 tracker, quorum, confchange, raftpb), `grpc-v3rpc` (etcdserver/api/v3rpc,
api/v3 etcdserverpb/v3rpc/version, v3lockpb/v3electionpb, grpc/*, protobuf/proto, net/http, sort),
`server-core` (etcdserver top-level, read, cindex, errors; pkg wait/idutil/notify/schedule),
`server-boot` (etcdserver/api membership, snap, v2stats, v3alarm, v3compactor, v3election,
v3lock (not their pb), storage top-level and wal, config, features), `rafthttp`, `apply-txn`
(etcdserver/apply, txn), `lease-auth` (lease, leasehttp, auth, bcrypt), `mvcc` (storage/mvcc,
pkg/adt), `backend-schema` (storage/backend, schema, pkg traceutil/pbutil/ioutil/httputil,
probing, rate, semver), `bbolt` (bbolt and its internals).

## Report

`notes/specs-only/verify/repair-<group>.md`: per finding (by its report and id): fixed (how,
files), fixed differently (why), not fixed (why: a pending user decision, needs another group's
file → the request). Then **Requests to <group>** sections, **New decisions** (a choice the user
should see, one paragraph each), and the build result. Final message: one line per finding, the
requests, the build status.
