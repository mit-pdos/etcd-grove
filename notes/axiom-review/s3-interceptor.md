# Axiom review: `grpc.ClientConn.NewStream.wp_proof` (interceptor-generic) and `grpcStreamerOk`

Reviewed 2026-11-26, worktree `/shared/etcd-grove-wt/s3int` at `0ce40a001d` ("wip s3int"), against
`origin/lean`'s previous form. Read-only review: nothing in the worktree was built or edited, and no
Lean was run. The only Go program is under `/shared/tmp/ps2/s3int/review/streamer/` (grpc-go v1.84.0
from the module cache, go1.26.0).

Targets:
- `Spec/google_golang_org/grpc/ClientConn__NewStream.lean:45-58`: `grpc.ClientConn.NewStream.spec`
  (WP form); the axiom is `Proof/google_golang_org/grpc/ClientConn__NewStream.lean:36`.
- `Proof/google_golang_org/grpc/InvGrpcStreamer.lean:167-187`: `grpcStreamerOk`, the trusted text.

## Verdict: survives

I found no counterexample. Every attack I tried is blocked by the Go code or excluded by a premise
(details below). Two documentation nits, neither a soundness issue:

1. The axiom's docstring (`Proof/google_golang_org/grpc/ClientConn__NewStream.lean:24-25`) still
   says "the stream interceptor (etcd's, at no retry) over grpc's streamer". The axiom is now generic
   over the interceptor, and etcd's case is the theorem `etcdNewStream_of`.
2. The axiom's docstring and the ledger entry (`notes/specs-only/ledger.md`, 2026-11-26) cite
   `notes/axiom-review/s3-interceptor.md`, which does not exist in the worktree. This report could
   become that file.

## Q1. Is the WP form true of grpc-go v1.84 on `grpcConn conn addrs ics [] Ok`?

**Yes.** `stream.go:256-265` (v1.84.0):

```go
opts = combine(cc.dopts.callOptions, opts)
if cc.dopts.streamInt != nil {
    return cc.dopts.streamInt(ctx, desc, cc, method, newClientStream, opts...)
}
return newClientStream(ctx, desc, cc, method, opts...)
```

- **The call options reach the callee unchanged.** `call.go:44-50`: `combine` returns `o2` itself
  when `o1` is empty, and `grpcConn … []` says the default call options are empty. A variadic
  `opts...` passes the same slice header.
- **The receiver is passed as `cc`.** Nothing else runs before the call. The callee's results are
  returned as they are.
- **`d.streamIc` is `cc.dopts.streamInt`.** `chainStreamClientInterceptors` leaves `streamInt` as
  the one `WithStreamInterceptor` function when no chained interceptors were given. No dial-option
  descriptor sets one (`InvDial.lean:9-44`, `streamIcOf`), and only `NewClient` makes
  `grpcConnOpts`.
- **The axiom gives no later credits.** It asks for the WP of the call directly, which is weaker
  than the real reduction needs. The caller proves the premise for every `str`, so the axiom never
  depends on which function grpc's `newClientStream` is.
- **Measured** (`streamer_test.go`, PASS): the interceptor receives `cc == conn` and the caller's
  exact `opts` (`&gotOpts[0] == &opts[0]`).

## Q2. Is `grpcStreamerOk` true of `newClientStream`?

**At no interceptor it is the old axiom's text, with two changes.**

**(a) Server-streaming descriptors are allowed whatever the interceptor.** The old form excluded
`ServerStreams` when an interceptor was set (`origin/lean` spec, the `d.streamIc = none` premise).
Its reason was that the *interceptor* may replay a server stream's sends to a second handler run.
That concerns the interceptor's own wrapper, not grpc's streamer: each streamer call is one
`newClientStream`, which is exactly what the old axiom claimed at no interceptor. A wrapper that
retries must now prove its own `cliStreamIs` from two streamer posts, each with its own fresh `γ`.
etcd's retrying wrapper is never proved: `streamIcOk` takes `ClientStreams = true` only
(`InvGrpcStreamer.lean:212`), and `Client__streamClientInterceptor.lean` takes the `Unimplemented`
branch at `max > 0`. So this change is sound.

**(b) The stream specification holds at every metadata.** The post is
`□ ∀ a md, a ∈ addrs → Spec a md γ (Dn a md)` (`InvGrpcStreamer.lean:186`). The old form required
`streamAttemptMd conn F om md` before the specification held. This is **justified by the
registration**:

- `isGrpcStreamsMd` at `a` is `isGrpcStreamMd a …` = `∃ hX π σ, grpcStreamSvcAt a …`
  (`InvGrpcStream.lean:1468-1472`).
- `grpcStreamSvcAt` (`InvGrpcWire.lean:505-513`) holds the table entry `(up₀, dn₀, spec₀)` with
  `□ ∀ md γ, spec₀ md γ (dn₀ md γ)` and `□ ∀ md γ Dn, spec₀ md γ Dn -∗ Spec md γ Dn`.
- So `Dn a md := dn₀ᵃ md γ` meets `Spec a md γ (Dn a md)` at *every* `md`, persistently.
- That `Dn` is the content the run actually delivers: `Server.Serve`'s axiom (`Server__Serve.lean:38`)
  converts the handler's responses to the entry's `dn₀ md γ` at the dispatched `md`. Both ends share
  `γ`.
- `grpcServesEnt` (`InvGrpcRun.lean:154-168`) makes every registered stream supply
  `□ ∀ md γ, Spec md γ (Dns md γ)` at every metadata. The only producers of `isGrpcStreamMd` are
  `isGrpcStreamMd_of_addr` and `_mono`, plus the two `Results`/`InvGrpcRun` lemmas that go through
  them, and all require the every-`md` fact.
- The registration is unique per address: `grpcAddrAt` stands on an `addrProto` invariant that holds
  the exclusive `netPend NG a S`, under the extension's own ghost names. `HasExt` is a `Prop` and
  `π` only names the connection registry, so a fresh `π` cannot fabricate a second table.

**Can a client exploit "every md"?**

- **Two different metadata.** Facts at `md₁ ≠ md₂` are about `Dn a md₁` and `Dn a md₂`. These are
  different contents, each meeting a specification the server already proved at every `md` and `γ`.
  The client gains nothing it could not get from the registration's own (hidden) witnesses.
- **Forcing a contradiction through `Spec`.** Suppose `Spec` pins `γ` (`⌜γ = γ₀⌝`), or owns ghost
  state at `γ`. Then the server could not prove `□ ∀ md γ, spec₀ md γ (dn₀ md γ)`, so no
  registration can exist.
- **Responses.** They come only at the actual dispatch `(a, md)` (the `Md` of `cliStreamIs`), so the
  extra `md`s never meet a received message.
- **A server-streaming descriptor.** See (a). The send-not-delivered caveat of `csAttempt.sendMsg`
  for `!ClientStreams` is the old axiom's and has not changed.

**Other claims of `grpcStreamerOk`, rechecked against `newClientStream` (`stream.go:302-…`):**

- **Fresh tokens per call.** `γ` is existential per call, so two calls get distinct `γ`. Measured:
  two calls in one interceptor, then four concurrent calls of the saved streamer after `NewStream`
  returned, each with its own handler run.
- **Metadata.** The post is `grpcAttemptMd conn om md` for the *streamer's* context's `om`. Measured:
  the second call's handler saw `k=[first second]`.
- **Call options.** `streamCallOptsOk` admits scalar options and etcd's `retryOption`, which embeds
  `grpc.EmptyCallOption` (its `before`/`after` do nothing). `newClientStream` prepends `OnFinish` on
  a copy (`append([]CallOption{…}, opts...)`), so the caller's slice is never written.
- **Errors.** Invalid outgoing metadata gives `status.Error(codes.Internal, …)` (`stream.go:322-335`).
  `waitForResolvedAddrs` returns `status.FromContextError(...)` or `ErrClientConnClosing`, both
  status errors. These are grpc's shape, as before.
- **After `Close`.** `idle.Manager.OnCallBegin` returns early once closed (`internal/idle/idle.go:193`).
  Measured: the saved streamer returns `Canceled … client connection is closing`, with no panic.
- **Persistence.** `grpcStreamerOk` is persistent, so an interceptor may call the streamer many
  times, concurrently, and after `NewStream` returned. Measured: all of these work in Go. The old
  claim "calls the streamer at most once, synchronously" is no longer needed.
- **Arguments the contract does not cover** cannot be proved, so they are no counterexample: a `cc`
  other than `conn`, a nil `desc` (`desc ↦□ sd` excludes it), a nil `ctx` (`GoInterfaceOk` with
  `ctxOk`), an unregistered method (`isGrpcStreamsMd`), or a descriptor with both flags false.

## Q3. What the new form allows that the old did not

- **Any interceptor whose call the caller can prove a WP for.** This is sound because the axiom
  states only what Go does: it calls `d.streamIc` with grpc's streamer. All trust moved into
  `grpcStreamerOk`, a statement about grpc's own function at no interceptor that the old axiom
  already made. The trust base shrinks: the axiomatized `streamIcMdIs` and the `streamMdOk`
  relation are gone (`InvDial.lean` diff). The old form let the axiom's post cover the
  interceptor's behavior, through `streamIcMdIs`, which etcd's (formerly axiomatized) interceptor
  introduced.
- **Server streams through an interceptor:** see Q2(a).
- **The specification at every `md`:** see Q2(b).
- **Consumers.**
  - `NewStreamNoIc_of` re-derives exactly the old triple at `d.streamIc = none`.
  - `etcdNewStream_of` goes through the proved `Client.streamClientInterceptor`.
  - That proof's `max = 0` branch passes the streamer's post through, only widening the error
    family to `True` and relating `om` by `etcdVersionMd`, and it maps the streamer's error to
    `cliOpenErr`. The `max > 0` branch returns `Unimplemented` because `ClientStreams` holds.
  - None of these consumers gets a stronger statement than the old axiom gave at the same
    connection, except the every-`md` fact, which Q2(b) justifies.

## Counterexample attempts (all failed)

| Attack | Why it fails |
|---|---|
| Interceptor passes a different `cc` or method, or a nil `desc`/`ctx` | Not in `grpcStreamerOk`'s precondition: no WP provable |
| Streamer called twice or concurrently, hoping for shared `γ` or tokens | `γ` existential per call; Go opens independent streams (measured) |
| Streamer used after `NewStream` returned or after `Close` | Go returns a status error (measured); no panic |
| Server-streaming descriptor through a retrying interceptor | Replay happens in the interceptor's wrapper, whose `cliStreamIs` must be proved; etcd's is excluded (`ClientStreams` premise) |
| Every-`md` specification to derive `False` from two metadata or a `γ`-pinning `Spec` | Registration already proves `spec₀` at every `md` and `γ`; a pinning `Spec` has no registration |
| Fake registration in a fresh net ghost instance | `addrProto` stands on the extension's exclusive `netPend NG a`; `HasExt` is a `Prop` |
| Caller's options slice mutated by grpc | `combine` returns it; `newClientStream` appends on a fresh slice |
| Invalid outgoing metadata from an interceptor-built context | `status.Error(codes.Internal, …)`, grpc's shape |

**Not tried:**
- The transport's own claims inside `cliStreamIs` (send/recv/CloseSend). They are unchanged from
  the old axiom and belong to `InvGrpcStream.lean`'s header and `Server.Serve`.
- A Lean proof attempt, since no Lean was allowed.

## Evidence program

`/shared/tmp/ps2/s3int/review/streamer/streamer_test.go`: an in-process server on `bufconn` with a raw
codec, and an interceptor that records `cc` and `opts`, calls the streamer twice (the second time
with added metadata), and saves it. The test then calls the saved streamer from four goroutines,
and once after `Close`. Output (PASS):

```
after Close: rpc error: code = Canceled desc = grpc: the client connection is closing
handler md k=[first]
handler md k=[first second]
handler md k=[first] (x4)
```

## Author's follow-up (2026-11-26)

Nit 1 fixed (the axiom's docstring now says "the stream interceptor dialed, if any (etcd's is proved)"); nit 2 fixed by this
file. The review was run by a fresh agent given the code and the questions, not the author's conclusions. Its Go test
(`streamer_test.go`, grpc-go v1.84.0) is kept below.

```go
package streamer

import (
	"context"
	"net"
	"sync"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/encoding"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/test/bufconn"
)

// a raw bytes codec so no generated stubs are needed
type rawCodec struct{}

func (rawCodec) Marshal(v any) ([]byte, error)      { return *(v.(*[]byte)), nil }
func (rawCodec) Unmarshal(d []byte, v any) error    { *(v.(*[]byte)) = append([]byte(nil), d...); return nil }
func (rawCodec) Name() string                       { return "raw" }

func init() { encoding.RegisterCodec(rawCodec{}) }

var mds = make(chan metadata.MD, 16)

func handler(srv any, ss grpc.ServerStream) error {
	md, _ := metadata.FromIncomingContext(ss.Context())
	mds <- md
	var b []byte
	if err := ss.RecvMsg(&b); err != nil {
		return err
	}
	return ss.SendMsg(&b)
}

var sd = grpc.ServiceDesc{
	ServiceName: "t.S",
	HandlerType: (*any)(nil),
	Streams:     []grpc.StreamDesc{{StreamName: "M", Handler: handler, ServerStreams: true, ClientStreams: true}},
}

func TestInterceptorArgs(t *testing.T) {
	lis := bufconn.Listen(1 << 20)
	s := grpc.NewServer()
	s.RegisterService(&sd, struct{}{})
	go s.Serve(lis)
	defer s.Stop()

	var gotCC *grpc.ClientConn
	var gotOpts []grpc.CallOption
	var saved grpc.Streamer
	ic := func(ctx context.Context, desc *grpc.StreamDesc, cc *grpc.ClientConn, method string, streamer grpc.Streamer, opts ...grpc.CallOption) (grpc.ClientStream, error) {
		gotCC, gotOpts, saved = cc, opts, streamer
		// call the streamer twice, with a different metadata the second time
		cs1, err := streamer(ctx, desc, cc, method, opts...)
		if err != nil {
			return nil, err
		}
		ctx2 := metadata.AppendToOutgoingContext(ctx, "k", "second")
		cs2, err := streamer(ctx2, desc, cc, method, opts...)
		if err != nil {
			return nil, err
		}
		_ = cs2.CloseSend()
		return cs1, nil
	}
	conn, err := grpc.NewClient("passthrough:///buf",
		grpc.WithContextDialer(func(ctx context.Context, s string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()),
		grpc.WithStreamInterceptor(ic))
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	opts := []grpc.CallOption{grpc.CallContentSubtype("raw"), grpc.MaxCallRecvMsgSize(1 << 20)}
	ctx := metadata.AppendToOutgoingContext(context.Background(), "k", "first")
	cs, err := conn.NewStream(ctx, &sd.Streams[0], "/t.S/M", opts...)
	if err != nil {
		t.Fatal(err)
	}
	if gotCC != conn {
		t.Fatalf("cc differs")
	}
	if len(gotOpts) != len(opts) || &gotOpts[0] != &opts[0] {
		t.Fatalf("opts not passed unchanged")
	}
	b := []byte("x")
	if err := cs.SendMsg(&b); err != nil {
		t.Fatal(err)
	}
	var r []byte
	if err := cs.RecvMsg(&r); err != nil {
		t.Fatal(err)
	}
	// the saved streamer, used after NewStream returned, concurrently
	var wg sync.WaitGroup
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			cs, err := saved(ctx, &sd.Streams[0], conn, "/t.S/M", opts...)
			if err != nil {
				t.Error(err)
				return
			}
			b := []byte("y")
			cs.SendMsg(&b)
			var r []byte
			if err := cs.RecvMsg(&r); err != nil {
				t.Error(err)
			}
		}()
	}
	wg.Wait()
	conn.Close()
	// after Close: an error, no panic
	if _, err := saved(ctx, &sd.Streams[0], conn, "/t.S/M", opts...); err == nil {
		t.Fatal("expected error after Close")
	} else {
		t.Logf("after Close: %v", err)
	}
	close(mds)
	for md := range mds {
		t.Logf("handler md k=%v", md["k"])
	}
}
```
