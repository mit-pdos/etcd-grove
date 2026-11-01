# The replies' size at `grpc.start` (2026-10-31)

A pair of trust-boundary axioms known false: `grpc.serve` and `grpc.serveStream` claimed serving
never panics, whatever a handler returns, while grpc v1.84 `make`s a reply's encoded length before
any size check and Go panics above `maxAlloc = 2^48`. The repair is a named workload premise taken
by the constructor of the tokens the two axioms consume. Drafted, reviewed three times, then approved
by the user with four decisions (`notes/reply-size.md`; `notes/decisions.md`, "The replies' size:
a workload premise on `grpc.start`"; `issues/etcd-txn-keysonly-reply-alloc-panic.md`).

## The first version (round 0, reviewed in round 1)

- **A handler contract**: each served method's handler gives, with its reply `m'`,
  `⌜Rep.wireLen m' ≤ 2^48⌝` (unary: in the handler's post; streams: in `Send`'s pre), and
  `grpc.serve`/`grpc.serveStream` rely on it.
- **etcd's handlers discharge it from the state**: a law "the live state is below the backend
  quota" derived from `BackendQuota.Available`, with a configuration premise `quotaEnabledOk`, bounding
  every Range/Txn reply.
- An issue claiming the panic reachable through a large keyspace.

## The critiques, and what each changed

1. **Round 1** (14 findings):
   - The quota law is false: etcd's applier applies an over-quota write and only flags it, and
     `Available` compares the bbolt file size, not the live state; the repository already has the
     quota as the named premise `apply.backendUnderQuota`. Dropped, with the configuration premise
     (stricter than the Go code).
   - Nested transactions multiply the arithmetic: the default configuration broke the draft's own bound.
   - The default `wireLen` (`grpcMsgMax ≤ 2^48`) made the handler obligation vacuous for every
     instance that kept it.
   - The reviewer argued the panic unreachable ("every etcd reply is built from fresh copies, so Go
     runs out of memory first") and the issue was dropped; it recommended (b), an opaque workload
     premise `grpcRepliesFit`, on `grpc.serve`/`grpc.serveStream`.
2. **Round 2** (6 findings):
   - **The fresh-copies argument was wrong**: etcd's keys-only ranges reference the index's own key
     slices (`FastKeysOnly`, `kvstore_txn.go:90-105`), so many ranges over the same keys in one
     nested transaction encode the same bytes many times, with a small heap. The panic is reachable;
     the issue was written (and reproduced: 12.8 GiB, a member crash). The premise's docstring now
     says what it is false of.
   - The premise is argued **per workload**, as its precedents are ("true of putget"), not per
     handler: it is true of every closed theorem's program.
   - **Placement**: the precedent (`backendUnderQuota` on `storage.NewBackendQuota`) puts the premise
     on the *constructor*, carried in the object it builds. Here that is `grpc.start`, the only
     producer of `grpcServerAt`/`grpcStreamServerAt`: one axiom restated instead of two, and no
     served result's statement changes.
3. **Round 3** (7 findings):
   - The premise goes on the programs' `Main.spec`s and the start-path lemmas, **not** "beside
     `Hbuq`" everywhere: `common/Serve.spec`, `StartServer`, `StartCompactingServer` and
     `authkv/startServer` take `Hbuq` but never reach `grpc.start`.
   - The served results rest on the premise only through the opaque token; their statements and
     `#print axioms` do not show it. Three options priced (docstrings, a transparent carrier, the
     premise on every served result); the user chose docstrings and file headers.
   - `grpc.Server.Serve.wp_proof`, which also consumes a token (`grpcServeTok`) and is where Go
     marshals, is also made true by the premise; its docstring says so.
   - No law turns a token back into `⌜grpcRepliesFit⌝`: a proof could otherwise discharge the
     premise inside the logic.
4. **The user's approval**: the design, global (not per server), the declined routes, docstrings
   only; and one correction from the landed issue: a nested all-reads transaction is **not**
   read-only (`IsTxnReadonly` checks the top level only), so it goes through raft under
   `--max-request-bytes`; the draft's "read-only transactions are the largest" was wrong for the
   nested case (a flat read-only one holds at most `--max-txn-ops` ranges).

## The approved spec

```lean
def grpcReplyMax : Nat := 2 ^ 48

/-- (opaque; a named workload premise, as `apply.backendUnderQuota`): every reply a gRPC server
of the run marshals encodes to at most `grpcReplyMax`. True of the closed theorems' workloads;
false of etcd under a client sending nested keys-only transactions over long keys. -/
opaque grpcRepliesFit : Prop

axiom grpc.start (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × val × GoInterface)) :
  grpcRepliesFit →
  grpcSrvNew gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
    |={⊤}=> grpcServerAt addr ics regs ∗ grpcStreamServerAt addr sics sregs ∗ grpcServeTok gs lis
```

`grpc.serve`, `grpc.serveStream` and `grpc.Server.Serve.wp_proof` unchanged in statement; the
tokens' docstrings say they exist only in a run satisfying the premise. `(Hrf : grpcRepliesFit)` on
the start-path lemmas (`etcd_kv_started`, `kv_served`, `wk_served`, `ak_served_kv`, ...), each
example's `Main.spec`, and the closed theorems.

## What it shows

- **A workload premise about what a resource's later operations do goes on the resource's only
  producer** and is carried by the resource, as `backendUnderQuota` by the quota object: the
  consumers' statements stay, and only the path to the producer changes.
- **Take a premise where the proof reaches its producer, not wherever a sibling premise sits**: a
  rule like "beside `Hbuq`" adds it to statements that never need it.
- **An argument that a size bound holds because the data are fresh copies must check every fast
  path for aliasing** (a keys-only branch reusing the index's slices): the encoding counts each
  reference, the heap does not.
- **Say what a premise carried by an opaque token makes conditional**: the results consuming the
  token rest on it invisibly; their headers say so, and no law extracts the premise from the token.
