# R11: a gRPC handler run's thread token (`grpc.serve`, `grpc.serveStream`) (2026-11-07)

**Reviewed** (branch `mvcc-api`, `a430dd8232`; the change and its argument: `notes/mvcc-merge/r11.md`):

- `grpc.serve` (`Proof/google_golang_org/grpc/InvGrpc.lean`): the method contracts now at
  `iprop(threadTok ∗ S)`, and `grpcServes … iprop(threadTok ∗ S)`; the runtime is still handed only
  the `n` copies of `S`, so each run's `threadTok` comes from nowhere in the logic (not from the thread
  fuel, not from the copies).
- `grpc.serveStream` (`InvGrpcStream.lean`) through `grpcStreamMethodOk(R)` (a run takes `threadTok`,
  the chain's post is `fun _ => threadTok`) and `grpcStreamHandlerOk` (the handler's continuation is
  `▷ ∀ err, threadTok -∗ Φ #err`); `etcdserverpb._Watch_Watch_Handler.spec` (`… ∗ threadTok ∗ …`, post
  `threadTok`).
- The author's caveat: sound only if grpc's handler goroutines count as live threads under
  `threadBound`, as the goroutines of a `go` statement do.

Go at the pins: grpc-go v1.84.0 (`examples/go.mod`), protobuf-go v1.36.12, toolchain go1.27.3.
Perennial's thread model: `.lake/packages/perennial/Perennial/GooseLang/{Threads,BoundedLang}.lean`,
`Lifting.lean` (`wp_fork_tok*`, `wp_ThreadExit`), the adequacy `goose_adequacy_start`
(`Proof/runtime/Start.lean`), `realThreadsBelow_of_one` (`Proof/runtime/Threads.lean`), and the
examples' instantiation (`Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/Adequacy.lean`).

## Verdict

**Refuted on the Go side, against the adequacy theorem's thread hypothesis; the Lean proof was not
built.** The caveat is exactly where it fails: grpc's handler goroutines are **not** live threads in
the sense the adequacy theorem bounds. `goose_adequacy_start`'s hypothesis is `RealThreadsBelow T n`,
on `state.threads` of the *model* execution; grpc's server goroutines are not in it (`Serve` is an
axiomatized call, its handler runs exist only inside the axioms), and the examples discharge the
hypothesis from the model's step count (`T = max (n + 2) srvRevokeK`, `realThreadsBelow_of_one`).
So a closed theorem can take `threadBound GF = T` with `T` small, while the real process runs any
number of handler goroutines, each of which the axiom hands a token. A program can turn "the live
handler runs hold tokens" into "fewer than `T` handler runs are live", which is false.

The give-back itself is enforced and cannot be gamed (below); the gap is only the token's source.

The same program refutes the pre-existing half of `grpc.serve` with no thread premise at all: the
`n` copies of `S` bound the concurrent runs (`at most n runs at a time`), `n` is the prover's choice,
and grpc-go does not wait for a slot. `notes/audit.md` lists this as **suspect** ("sound while the
slots stand for a bound Go cannot reach (about 2^30 concurrent runs)"); nothing in the axiom ties `n`
to such a bound, so it falls at `n = K - 1` (section "The slot bound").

## How Perennial accounts threads

- There are `T - 1` thread tokens in all (`Threads.lean`, the header): the main thread's, and `T - 2`
  in the thread fuel the state interpretation owns. `Fork` takes one from the fuel (stutters at fuel
  `0`), `ThreadExit` returns one; `threadToks T ⊢ False`.
- The adequacy theorem starts the fuel at `T - 2` and needs the real execution's **model** thread
  count below `T` (`RealThreadsBelow`); `bounded_step_of_real` then shows every real `Fork` is a
  bounded one. Nothing else limits `T`.
- So "a token per live goroutine" is a theorem of the model only for goroutines the model forks. A
  token the axiom hands a run is backed by no `Fork`: the axiom asserts that, whenever a run starts,
  some slot below `T - 1` is free, i.e. model threads plus live runs stay below `T`. Nothing in the
  closed theorems' hypotheses says so.

## The attack

```go
package threadtok

const K = 1000

var active int64
var ready = make(chan struct{})
var block = make(chan struct{})

func hold(srv any, ctx context.Context, dec func(any) error, ic grpc.UnaryServerInterceptor) (any, error) {
	req := new(emptypb.Empty)
	if err := dec(req); err != nil {
		return nil, err
	}
	if atomic.AddInt64(&active, 1) == K { // the run's token goes into the invariant here
		close(ready)
	}
	<-block // never closed: the run stays live, its token in the invariant
	return new(emptypb.Empty), nil
}

var desc = grpc.ServiceDesc{ServiceName: "threadtok.T", HandlerType: (*service)(nil),
	Methods: []grpc.MethodDesc{{MethodName: "Hold", Handler: hold}}, Streams: []grpc.StreamDesc{}}

func Main(lis net.Listener) {
	s := grpc.NewServer()
	s.RegisterService(&desc, struct{}{})
	go s.Serve(lis)
	<-ready
	if atomic.LoadInt64(&active) >= K {
		panic("K live handler runs: more than threadBound thread tokens")
	}
}
```

**Go.** `TestPanics` runs `Main` alone in a child process (the verified program: two model threads,
main and `Serve`'s) and makes `K` concurrent `Invoke`s from the test process (the environment, over
10 connections). grpc-go starts every handler (`server.go:1089-1106`: `go f()` per stream; the
per-connection quota is `MaxUint32` by default, `server.go:189`), the `K`-th closes `ready`, `Main`
panics. Output (`go test -count=1 -v -run TestPanics`, go1.27.3, grpc v1.84.0), every time (10/10
with `-count=10`):

```
=== RUN   TestPanics
    threadtok_test.go:72: server process exit: exit status 2
        stderr (head):
        panic: K live handler runs: more than threadBound thread tokens [recovered, repanicked]
        ...
        example.com/axiomcx/threadtok.Main({0xf25220, 0x25146afcd800})
        	/tmp/axiomcx-r11/threadtok/threadtok.go:52 +0xe5
--- PASS: TestPanics (0.10s)
```

(The program and test were run in a scratch module, `/tmp/axiomcx-r11` with `examples/go.sum`; not
committed. The program is above; the test is the obvious harness.)

**The proof that it does not panic** (not built; the steps, each a standard Iris step):

1. Triple `{{ isPkgInit threadtok ∗ ⌜threadBound GF ≤ K⌝ }} Main lis {{ True }}`, the premise in the
   style of `ServedLease`'s `HT : threadBound GF ≤ 2 ^ 30 - 1`.
2. Invariant `I := ∃ k, active ↦ k ∗ threadToks k` (atomic cell).
3. `grpc.serve` at `S := emp`, `n := 0` (or any `n`), the method `hold` meeting
   `grpcMethodOkMd … iprop(threadTok ∗ emp) …`: the handler opens `I` at the `AtomicAdd`, deposits the
   run's `threadTok` (`threadToks k ∗ threadTok ⊢ threadToks (k + 1)`, `threadToks_add`); `<-block`
   on a channel nobody closes or sends to never returns, so the post (which would need the token back)
   is never due. The `close(ready)` branch is unreachable: after the deposit `threadToks (k + 1) ⊢
   ⌜k + 1 < T⌝`, and `T ≤ K`, so the new value `k + 1 ≠ K` (no channel spec needed for `ready`).
4. `Main` (holding its token): after `<-ready` (nothing to learn from it), open `I` at the load:
   `threadToks (k + 1) ⊢ ⌜k + 1 < T⌝`, so `k < K`: the `panic` branch is dead.
5. Closed theorem: `goose_adequacy_start` at `T := K`; `RealThreadsBelow K n` for `n ≤ K - 2` from
   `realThreadsBelow_of_one` and `realThreadsBelow_mono`. The real run reaches the panic in far fewer
   than `998` model steps of `Main` (a handful of translated calls, a blocked receive, a load), and its
   model thread count is 2. The theorem says no thread panics; Go's main thread does.

Why not built: no closed proof yet serves a custom gRPC service (`grpc.serve`'s only users are
v3rpc's and client/v3's `Results`); it needs a `ProtoMsg` instance for `emptypb.Empty`, the
server-construction specs (`NewServer`, `RegisterService`, `grpc.start` under `grpcRepliesFit`,
`Serve`), the handler's generated-code proof and a Goose project for the package. None of it is
where the claim fails; step 3 is the whole point, and it uses only the new resource of the run.

## The slot bound (pre-existing, not R11's)

The same program refutes `grpc.serve` without the thread premise: take `S` an exclusive ghost slot
(one of `K - 1` tokens of a ghost set) and `n := K - 1`. The handler deposits its slot with the
increment; `I := ∃ k, active ↦ k ∗ k slots` gives `k ≤ K - 1 < K`. The axiom's "a run holds one copy
… at most `n` runs at a time" is false of grpc-go: it starts every stream's handler, with no
application-level slot (the only limit is `MaxConcurrentStreams`, per connection and per server
option). The stream side states the same for its pool ("the runtime starts a stream when the pool
holds a copy"). `notes/audit.md` already has both as *suspect*; this program makes them concrete at
`n = 999`.

## Attacks that failed (the run's own discipline is sound)

- **Returning without the token.** Unary: `grpcMethodOkMd`'s post returns the run's resource, here
  `threadTok ∗ S`; a returning run must give a token back. Stream: `srvStreamChainWP … (fun _ =>
  threadTok)` and `grpcStreamHandlerOk`'s `▷ ∀ err, threadTok -∗ Φ #err`; the interceptors'
  early-error branch must also produce `Ψ #err`, which now owes the token. Tokens are exclusive
  (`levelTokList_not_mem`), so none can be returned twice or duplicated by a continuation (it is used
  once, linearly).
- **Stashing the token and returning another.** A handler may put its token in a channel or an object
  and return one it took from elsewhere. Tokens are fungible in Perennial too (a `WaitGroup`'s
  invariant holds tokens of other goroutines): the stashed token stands for the goroutine whose token
  was taken, which is live and no longer holds one. The count "tokens ≤ live goroutines" is kept;
  same as a `go` statement's token.
- **A run that never returns keeping its token.** Its goroutine is live (blocked); a `go` statement's
  thread does the same. Not by itself the flaw; the flaw is that this goroutine is not a model thread.
- **Nested calls** (a handler calling the same server) multiply runs and tokens, but each nesting
  level is a real goroutine too; it only matters through the same source gap.
- **An inconsistent axiom.** No `⊢ False` for every `T`: the runs a finite execution has are finite,
  and at a large enough `T` the tokens fit. The axiom is contradictory only at small `T`, which is
  what the counterexample exploits through a closed theorem's choice of `T`.

## Effect on the current results

The closed theorems' thread premises are large (`threadBound GF ≤ 2 ^ 30 - 1`, `≤ backend.rdPoolN =
2 ^ 28`, `≤ 2 ^ 31`): a real violation of a bound they protect (Go's `RWMutex` reader count, the
backend's reader pool) needs about `2 ^ 28` live handler goroutines at once, beyond any machine's
memory. No exported result is practically affected. The closed theorems are formally too strong: they
hold "for every execution with fewer than `T` model threads", while R11's argument needs `T` to bound
grpc's goroutines as well, and the `T` they take is the model's step count plus two.

## Proposed restatement (not applied)

Make the premise the argument rests on explicit, as `grpcRepliesFit` does for reply sizes:

- an opaque workload premise `grpcRunsFit T` ("at any time, the live handler goroutines of the
  process's gRPC servers plus the program's live threads are below `T`"), carried by `grpc.start`'s
  tokens like `grpcRepliesFit`, and taken by the closed theorems that serve gRPC, with `T` the
  theorem's thread bound. The closed theorems then say nothing about runs with too many concurrent
  calls, which is honest; and they should fix `T` as that bound, not as `n + 2` (the generic
  `realThreadsBelow_of_one` choice is fine for model threads but not for this premise).
- or keep a run's token from a stocked source (the pre-R11 form), with the server's thread pool
  growing as it serves (it cannot, which is why R11 was made).

For the slot bound: the same kind of premise for `n` (the concurrent runs a workload makes are below
`n`), or drop the per-run slot from the unary axiom where Go has none. Suggested `notes/audit.md` row
for `grpc.serve`/`grpc.serveStream`: **refuted on the Go side** (`notes/axiom-review/r11-grpc-threadtok.md`):
the run's token (R11) and the `n` slots both bound concurrent handler runs, which grpc-go does not.
