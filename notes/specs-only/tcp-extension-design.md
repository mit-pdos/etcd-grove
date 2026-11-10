# The network as a TCP extension, with grpc-go and net/http as trusted Go models over it (design for review)

Design note, 2026-11-10 (specs-only at `85668bb573`), **for the user's review: nothing here is
built**. It replaces `net-extensions-design.md` (one `"net"` extension whose 39 operations were
HTTP exchanges and gRPC streams as records, with a preface trick to see through etcd's connection
wrappers), following the user's decisions of 2026-11-10 (`open-questions.md`, "The user's
answers", last item): **a TCP extension** (byte streams; a node's crash closes its connections;
listening addresses survive per the node's address plan), with **grpc-go and net/http as trusted
Go models written over it**, so that etcd's own wrappers run as translated code on real
`net.Conn`s; at-most-once, grpc's transparent-retry conditions, status codes and C5's table of
grpc's own messages live in the grpc model; handler panics are program panics; members reuse a
slot's peer and client URLs across re-adds; the client node never crashes. No Iris axioms: what
is trusted is the extension's semantics and the models' code.

Drafts (not in the repository, not in Perennial), at `/home/ubuntu/.claude-E/jobs/b4c3a1d2/tmp/tcpext-draft/`:

* `Impl.lean`: the TCP extension's semantics, 332 lines, 7 operations; **typechecks** against
  the pinned Perennial (`lake env lean`, from the worktree root). Section 2 summarizes it; the file
  is the precise statement.
* `modelframe/frame.go`: the framing both models put on their connections (section 4.2); compiles,
  `go vet` clean, and a test round-trips a call head and checks the size limit over a real
  loopback TCP connection read a byte at a time.
* `grpc_model_sketch.go`, `http_model_sketch.go`: the shape of the two models (not compiled:
  they are fragments of patches of grpc-go's and net/http's packages).

Contents: 1. the layers; 2. the TCP extension; 3. what runs between `net` and the models; 4. the
grpc and net/http models; 5. the previous design's inventory, and what becomes provable where;
6. sizes and risks; 7. open choices.

## 1. The layers

| layer | what | trusted? | where |
|---|---|---|---|
| T | **the TCP extension**: sockets, listeners, byte pipes; 7 operations | yes (semantics) | `GooseLang/Ext/Tcp/{Impl,Specs,Adequacy}.lean`, named `"net"` |
| N | **Go's `net`** over T: `net.Listen`, `(*Dialer).DialContext`, `(*TCPListener).Accept`, `(*TCPConn).Read`, ... | yes (hand-written GooseLang, as `os`) | `TrustedCode/net.lean`; `Code/net.toml` translates the types and the pure code |
| W | **the program's wrappers**: etcd's `client/pkg/transport` (`timeoutConn`, `rwTimeoutDialer`, `keepaliveListener`, `LimitListener`), cmux, rafthttp's transports, `xiang90/probing` | no (translated) | `Code/` |
| M | **the models**: grpc-go and net/http as Go code over `net.Conn`: their transports, servers, client connections, framing | yes (Go code, a patch of each real package) | `etc/model-patches/{grpc-go,go}/*.patch`, translated by goose |
| R | **the libraries' own simple code**, reached through M: grpc's `status`, `codes`, `metadata`, `peer`, `resolver`, `resolver/manual`, `health`, option constructors, `invoke`, interceptor chaining, generic stream wrappers; net/http's `Header`, `textproto`, `NewRequest`, `StatusText`, `ServeMux`, `DetectContentType`; `net/url` | no (translated) | `Code/` |
| P | protobuf (`proto.Marshal`/`Unmarshal`, called by the codecs, which are program code) | E2's, not the network's | |

What changes from the previous design, in short: the trusted semantics shrinks from 39 operations
over HTTP and gRPC records to 7 TCP operations; HTTP and gRPC become Go code that frames bytes; the
preface trick (its C1) goes, since the models read and write every byte through whatever
`net.Conn` the program hands them; the crash story becomes "the node's fd table is emptied"
(no incarnation numbers, no takeover of records).

## 2. The TCP extension (`Impl.lean`)

### 2.1 A new extension, not Grove's

Perennial's Grove extension (`Ext/Grove`) has `Listen`, `Connect`, `Accept`, `Send`, `Receive`,
but it is **message-based**: each endpoint has a *set* of messages, so a receive may return any
message sent, any number of times (duplication, reordering, loss); its endpoints are `w64`, not
address strings; `Listen` binds nothing and `Accept` returns a connection to *any* remote
endpoint; it has no close, end of file or error but a flag; it bundles files and clocks
(`FileWrite`, `GetTSC`), which overlap OsFs (this repository's file extension); and its crash makes
the node's state anything. TCP's guarantee is the opposite of a message set: one in-order,
exactly-once byte stream per connection. Making Grove's operations TCP's would change the
semantics gokv's proofs rest on. Perennial's toy `Ext/Net` (message sets per address string) is
not a TCP model either. So: **a new extension**, in this repository first (as OsFs), named after
the Go package it implements (`"net"`), proposed to Perennial once it has carried a proof (U9).

### 2.2 State

**Local** (per node, like a process's fd table): `Local = {node : Nat, fds : GMap w64 FdEnt}`,
`FdEnt = {sock : Sock, closed : Bool}`, `Sock = lis l | conn c side`. A closed fd stays in the table
(marked), so its number is never reused within the process's life: Go's `poll.FD` makes a closed
`net.Conn`'s later operations return `ErrClosed`, never act on another socket, and the model gets
the same without racy Go-side state.

**Global** (the network): `Global = {plan, bound, lis, conns, next}`:

* `plan : GMap GoString PlanAddr`, **the deployment**: every address string the program may listen
  at or dial, with the node that may listen at it and its parsed `(ip, port)` (what
  `LocalAddr`/`RemoteAddr` report; the end theorem's instance checks by `decide` that the string is
  the text of `ip:port`). Fixed: no step changes it (as OsFs's fixed domain of paths).
* `bound : GMap GoString Nat`: each address's last-bound listener (it may since have been closed,
  or belong to a dead process).
* `lis : GMap Nat {addr, isOpen, backlog : List Nat}`: listeners; the backlog holds the
  connections dialed to it and not yet accepted, oldest first.
* `conns : GMap Nat {dAddr, aAddr, up, dn}`: connections, each with the dialer's local address
  (chosen at the dial), the listener's address, and two pipes `Pipe = {data : List w8, rd : Nat}`
  (the bytes written so far in that direction, and how many the reader consumed).
* `next`: fresh identities.

### 2.3 Operations

Results as `syscall`'s: `(#value, #errno)`, `0` success. `EBADF` means exactly "this process
closed the fd" (Go's `ErrClosed`); `eDeadline` (not an errno) is the poller's deadline (Go's
`os.ErrDeadlineExceeded`); every other failure is any errno in `Fails`: nonzero, not `EINTR`
(Go retries it), not `EAGAIN` (Go waits in the poller), not `EBADF`; `accept`'s also not
`ECONNABORTED` (Go retries it).

| op | `value ↦ result` | step (stuck cases last) |
|---|---|---|
| `Listen` | `#a ↦ ((#fd, (ip, port)), #e)` | if `Bindable` (nothing bound at `a`, or the bound listener is held by no open fd of this process: closed, or a dead process's): a new open listener bound at `a`, at a fresh fd; or any `Fails` errno (`EADDRINUSE`, ...), and only that if this process holds the bound listener open. **Stuck** unless `a` is this node's in the plan. |
| `Accept` | `#fd ↦ ((#fd', remote), #e)` | the oldest backlog connection, its acceptor end at a fresh fd, with the dialer's address; or an `AcceptFails` errno at any time; `EBADF` once closed; **waits**. Stuck on a non-listener fd. |
| `Dial` | `#a ↦ ((#fd, local), #e)` | if the listener bound at `a` is open (a dead process's included): a new connection appended to its backlog, the dialer's end at a fresh fd, the local address any; or any `Fails` errno (refused, unreachable, timed out), the only outcome if nothing open is bound; **waits**. **Stuck** unless `a` is in the plan. |
| `Read` | `(#fd, #n) ↦ (#bytes, #e)` | `n = 0`: `([], 0)` at once (Go's `poll.FD.Read`). Else: 1..n of the unread bytes; **end of file `([], 0)` whenever the reader has consumed everything written so far**; or a `Fails` errno (including `eDeadline`) at any time; `EBADF` once closed; **waits**. Stuck on a listener fd. |
| `Write` | `(#fd, #d) ↦ (#k, #e)` | all of `d` appended (`k = len d`, `0`); or a prefix of `j` bytes appended and a `Fails` errno (`k = j`, any `j ≤ len d`); `EBADF` once closed; **waits**. A write after the peer closed or died may succeed (no one reads it) or fail. |
| `Close` | `#fd ↦ #e` | the fd is closed (a blocked `Accept`/`Read`/`Write` on it then returns `EBADF`); a listener stops taking dials (its backlog is never accepted); a connection end needs nothing more (the peer may see end of file once caught up, as always). `EBADF` if already closed. |
| `Check` | `#fd ↦ #e` | `0` if open, `EBADF` if closed. What the deadline and socket-option setters do. |

The heap never changes. Stuck also: an fd not in the table.

### 2.4 Crash

`TcpCrash σ σ' := σ'.node = σ.node ∧ σ'.fds = ∅`: the process is gone, its kernel closed its
sockets, the node keeps its index (its plan addresses are still its own). DistLang's crash cannot
change the global state ("a crash changes neither the other nodes nor the global state"), so the
dead process's listeners and connections stay in it, **held by no fd**: nothing can act on them
again. What follows, for each requirement of `pernode-crash-plan.md` §2.3:

* **N1** (a crash ends the node's listeners, connections and handlers; addresses survive): its
  threads are gone (DistLang), its sockets unreachable (no fd); its addresses are still its own in
  the plan, and its next `Listen` of one rebinds it (`Bindable`: the bound listener is held by no
  open fd of the new process). The dead listener is not touched: it is merely no longer bound, so
  new dials go to the new one; dials made in between landed in its backlog, which nothing accepts
  (Linux refuses them: an extra behavior, T5).
* **What the peers see** is what the step rules always allow: the dead side's bytes written before
  the crash, or a prefix of them, then end of file (a process kill: the kernel's FIN after the
  data), an error (its RST, or the reset a rebooted machine answers), or nothing (a power loss,
  until a timeout, which is an error). Since a peer cannot know whether the other side is alive,
  the rules allow those outcomes on every connection at all times (T3). A crashed server never
  sends a reply it did not write before the crash: **N4**.
* **N5** (at most once across the server's crash): the new process cannot read the old
  connections (no fd), and its listener receives only new dials; resends are the models' rules
  (section 4), which resend only what provably was not dispatched.
* The client node never crashes (the user's Q1, a Perennial change to `DistLang`): nothing here
  depends on it.

The draft also states the start: `LocalInit i σ := σ.node = i ∧ σ.fds = ∅` and
`GlobalInit plan g` (the plan; nothing bound; no sockets).

### 2.5 The Go API it backs (`TrustedCode/net.lean`, layer N)

Hand-written GooseLang over the operations, in `TrustedCode/os.lean`'s style (each docstring the
Go source it replaces and why it is faithful), with the trusted layout `netFD = struct{ sysfd int;
laddr, raddr Addr }` (Go's `netFD` holds a `poll.FD` and the addresses), and Go's own types
translated over it (`TCPListener{fd, lc}`, `TCPConn{conn{fd}}`, `TCPAddr`, `OpError`, ...):

| Go | model |
|---|---|
| `net.Listen(network, a)`, `(*ListenConfig).Listen` (`Control == nil`) | `network` `"tcp"`/`"tcp4"` (else stuck); `Listen`; a `*TCPListener`, or `&OpError{Op: "listen", Net, Addr, Err: os.NewSyscallError("bind", errno)}` |
| `(*TCPListener).Accept`, `AcceptTCP`, `Close`, `Addr` | `Accept` (a `*TCPConn` with both addresses: what etcd's `keepaliveListener` type-asserts), `Close`, the stored address; errors as Go wraps them (`ErrClosed` for `EBADF`; `Temporary()` from the errno, as Go's) |
| `net.Dial`, `DialTimeout`, `(*Dialer).Dial`, `DialContext` (`LocalAddr`, `Control` nil) | ctx done first: Go's `mapErr(ctx.Err())`; else `Dial`; a failure while ctx is done: the ctx's error, as Go's `DialContext`; `Timeout`, `Deadline`, `KeepAlive` change nothing (failures are always possible) |
| `(*conn).Read`, `Write` | `Read` (a zero read is `io.EOF`), `Write`; errors `&OpError{Op: "read"/"write", Net, Source, Addr, Err}` over `os.NewSyscallError`, `ErrClosed`, `os.ErrDeadlineExceeded` |
| `(*conn).Close`, `LocalAddr`, `RemoteAddr` | `Close`; the stored addresses (valid after `Close`, as Go's) |
| `SetDeadline`, `SetReadDeadline`, `SetWriteDeadline`, `(*TCPConn).SetKeepAlive`, `SetKeepAlivePeriod`, `SetNoDelay`, `SetLinger` | `Check` (`nil`, or `&OpError{Op: "set", ...ErrClosed}` once closed); deadlines are not tracked (T4) |
| `CloseWrite`, `CloseRead`, `File`, `SyscallConn`, unix sockets, UDP | not modelled (stuck): nothing on the path uses them (the models need no half-close) |

Translated real code beside it: `TCPAddr.String`, `IP.String`, `SplitHostPort`, `JoinHostPort`,
`OpError`'s methods, the error variables.

### 2.6 Justification against Linux TCP, and the known gaps

| rule | why Linux (and Go over it) does this |
|---|---|
| a connection's bytes arrive in order, once, intact, to the other end's holder only | TCP's sequence numbers, retransmission and checksums; the test's deployment is loopback, which has no loss at all |
| a read returns 1..n of the buffered bytes | `recv` on a `SOCK_STREAM` returns what is queued, at most `n`; Go's `Read` makes one such call |
| end of file only once the reader has every byte written before it | the FIN is sequenced after the data, whether sent by `close` or by the kernel when the process dies |
| errors at any time; data accepted by `write` may never arrive, but never with a gap | RST (a close with unread data, a dead or rebooted peer), retransmission and keepalive timeouts, `EPIPE`; after a reset no later byte is delivered |
| a write appends all, or a prefix and fails | `send` copies into the send buffer; Go's `poll.FD.Write` loops until all is written or a call fails, and reports the count |
| `listen` binds a dead process's address again | the dead process's listening socket closed with it (its accept queue reset); Go sets `SO_REUSEADDR` on listeners, so `TIME_WAIT` connections do not block the bind |
| a dial lands in the listener's accept queue, accepted oldest first | the kernel completes the handshake into the accept queue whether or not the process accepts; `accept` returns the oldest |
| fds are per process, closed at its exit; a crash leaves the network as it was | the kernel; DistLang's crash is local |

**Known gaps** (over-approximations are sound for safety; the rest are environment assumptions or
things the proof must show are not reached):

* **T1. No corruption.** TCP's 16-bit checksum can miss errors on a real network; loopback has
  none. An environment assumption.
* **T2. Unbounded buffers.** Writes never block for flow control and data is visible to the peer
  at once: extra interleavings only.
* **T3. End of file whenever caught up, failures not sticky.** A live writer is indistinguishable
  from a dead one (U1), so a reader may see end of file at any moment it has read everything, and
  read again later; a failure changes nothing. Real TCP gives neither on a live connection. No
  proof needs to exclude them: the models' framing is self-delimiting and nothing above the models
  reads a raw connection to its end.
* **T4. No time.** Deadlines are not tracked: any blocking operation may report one (U5). Keepalive,
  `Dialer.Timeout`, net/http's and grpc's timers only ever cause failures, which are always possible.
* **T5. A dial to a dead process's listener** may succeed into a backlog nobody accepts (Linux
  refuses it): an extra behavior.
* **T6. Outside the model (stuck):** addresses outside the plan (aliases such as `localhost` for
  `127.0.0.1`, port `0`, IPv6 forms), unix sockets, `Control` hooks, half-close, `File()`, urgent
  data.
* **T7. The deployment is closed:** nothing else on the machines binds or dials the plan's ports
  (as OsFs's "no other process touches the files").
* **T8. Resource exhaustion** beyond errnos (out of memory, the runtime's fatal errors; the first
  socket starts Go's netpoller, whose failure is fatal: OsFs's open gap applies here too).
* **T9. Accept-queue overflow** (dropped SYNs) is a dial that fails or waits.

### 2.7 The extension's ghost state (Specs, internal; sketched for feasibility)

* **Global start** (`Hstart`, N3): `planAt a pa` (persistent) and one `tcpFree a` per plan address;
  `tcpReserve : tcpFree a ==∗ tcpProto a P` fixes, once for the run, the **byte protocol** every
  connection dialed to `a` follows (a predicate pair on the two directions' frame sequences, with
  the resources each frame carries). One protocol per address for the whole run, as the per-node
  crash plan requires (§2.3 there).
* **Local start and `crashStart`** (N2): the generation's fd table (empty) and `listenRight a` for
  each of the node's plan addresses, exclusive within a generation. Nothing global changes at a
  crash, so the crash interpretation is only that.
* **Per direction of a connection**: the writer's exclusive `pipeW γ bs` (the bytes written so far)
  and the reader's exclusive `pipeR γ k`; a persistent lower bound on the writer's history for the
  reader. `Dial` and `Accept` hand out each end's two halves with the address's protocol attached.
  `Write` is an atomic update of `bs`, so a frame layer can deposit a frame's resource at the step
  that completes it.
* **N6**: every handler run is a goroutine the models fork, so the handler-pool premise folds into
  the theorem's thread bound `T`.

## 3. What runs between `net` and the models

The models call `net.Listener.Accept` and `net.Conn.Read`/`Write`/`Close` on the values the
program gives them, and dial through the dialer the program configured, so whatever wraps a
socket runs as translated code (layer W): etcd's `rwTimeoutDialer` and `timeoutConn` (a deadline,
then the inner call), `keepaliveListener` (`*TCPConn` assertion, keepalive setters: `Check`),
`LimitListener` (a slot released by the connection's `Close`), cmux (its matchers read the first
bytes through the base connection and its `MuxConn` replays them to the matched listener's
server, section 4.5).

**On the end theorem's path** (`examples/etcd/crashreconf`): a member listens with `net.Listen`
directly and serves `http.Serve(pl, etcdhttp.NewPeerHandler(lg, s))` and `grpc.Server.Serve(cl)` on
the raw listeners, so no keepalive listener, `LimitListener` or cmux; rafthttp's transports
(`transport.NewTimeoutTransport`: an `http.Transport` whose `Dial` is the timeout dialer,
`MaxIdleConnsPerHost` -1 for the stream round tripper, a unix transport registered with
`RegisterProtocol` and never used), etcd's `cluster_util.go` clients and the prober
(`xiang90/probing`, translated) are; clientv3 runs on every node (the client node, and each member
node's `waitAdded`/`removed`). etcd's `embed` path (cmux and the wrappers) works the same way and
is not needed for the theorem.

## 4. The grpc and net/http models (layer M)

### 4.1 How they are written: patches of the real packages (U2)

Each model is **a patch of the real package's Go source**: grpc-go v1.84.0 (the examples' pin)
and Go 1.27.3's `net/http` (`etc/goose.py`'s `GO_TOOLCHAIN`), kept as
`etc/model-patches/{grpc-go,go}/*.patch`. A patch adds unexported files (the framing, the
transports) and replaces the bodies of the reached functions that the real package implements with
its HTTP/2 transport, balancers, connection pool and channelz (`Server.Serve`, `GracefulStop`,
`Stop`, `NewClient`, `newClientStream`, `Transport.RoundTrip`, `Server.Serve`, `Shutdown`, ...),
adding fields to structs where needed (never removing any, so that the rest of the package
compiles). Everything else stays the real code (layer R), translated untrusted. `etc/goose.py`
applies the patches to the pinned sources before translating (as it applies the prophecy patches,
but these are unrestricted and trusted), for `net/http` through an overlay of the toolchain's
source.

Why this shape: the API is the real one by construction (every type, field and option etcd's
translated code and its dependencies reference typechecks, with nothing to keep in sync); the
trusted part is exactly the diff, reviewable as Go against grpc-go's and net/http's own code with
the same names and structure; the reused code is real and verified; and **the program can run over
the models** (`replace google.golang.org/grpc => <patched tree>`, `go test -overlay` for
`net/http`), a check that the models are not vacuous: crashreconf's porcupine test over the models,
and unit tests of each model's rare paths. The alternatives (U2): hand-written GooseLang
`TrustedCode` (as `os`, about 3000 lines of GooseLang to review and nothing to run), or shadow Go
packages with only the reached API (every dependency of the translated packages that imports grpc,
`otelgrpc`, grpc-gateway, the prometheus interceptors, would have to typecheck against them).

**Nondeterminism in Go code.** A model's choice point (refuse this stream? pick which address? go
idle? resend?) is `modelChoose()`, one trusted declaration per model package: its GooseLang body
is an arbitrary boolean (any value, so the model has both behaviors), its Go body `false` unless a
test knob randomizes it, so that a real run takes the common path. Address picks use the same with
an index (`modelChooseN(n)`). This is the only hand-written GooseLang in layer M.

**Outside the model**, a model panics with "not modelled" (the adequacy theorem's no-panic
conclusion then makes the proof show it unreached): TLS and any transport credentials but
`insecure`, a service config other than `{"loadBalancingPolicy": "round_robin"}`, `ServeHTTP`,
HTTP redirects, `https`, `Hijack`, 1xx responses, HTTP/2 over TLS.

### 4.2 The framing (`modelframe/frame.go`)

After the protocol preface, a connection carries frames `kind:u8 length:u32be payload`; strings and
byte strings are length-prefixed, metadata and headers `count (key, count, values...)`. Each frame
batch goes out in one `Write`, so a failed write tells the writer how much reached the peer, and a
writer abandons the connection after a failed write. A reader reads a frame's 5-byte header,
checks the length against its limit **before allocating** (grpc's `MaxRecvMsgSize` check sits there,
as grpc-go checks its own length prefix), then the payload; partial reads are handled in one
function (`readFull`, `io.ReadFull`'s contract) and nowhere else. A standard-library package cannot
import a module, so each patch carries its own copy (I4).

| connection | client to server | server to client |
|---|---|---|
| gRPC (one stream per connection) | HTTP/2's 24-byte client preface `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`; `GHead` (method, timeout, metadata); `GMsg` (a codec's bytes); `GClose` (`CloseSend`); `GCancel` (the client's `RST_STREAM`) | `GRefused` (never dispatched; then close); `GHeader` (header metadata); `GSMsg`; `GTrailer` (code, `grpc-message`-encoded message, trailer metadata) |
| HTTP (one request per connection) | the real request line `METHOD RequestURI HTTP/1.1\r\n`; `HHead` (host, path, raw query, content length, header); `HChunk`*; `HEnd` or `HAbort` (the body's `Read` failed) | `HResp` (status, header); `HRChunk`*; `HREnd` (the handler returned) |

One stream (request) per connection (U3) removes stream identifiers, multiplexing, flow control
and the connection pool, at no cost to what the program observes (section 4.6): grpc-go and
net/http also open fresh connections, the remote address is any anyway, and net/http's resends of
requests on reused connections are kept as resends (4.4).

### 4.3 The grpc model

**Server** (sketch: `grpc_model_sketch.go`). `NewServer`: the real option constructors applied to
the real `serverOptions` (codec, size limits, interceptor chains; keepalive, `MaxConcurrentStreams`,
the enforcement policy are parsed and unused), the real `chainUnaryServerInterceptors`/
`chainStreamServerInterceptors`; channelz, tracing and server workers removed. `RegisterService`:
the real registry and its duplicate check (a panic in place of `logger.Fatalf`); the reflection
check of the handler type is skipped (goose has no `reflect`; continuing where grpc-go exits is a
superset, previous G8). `GetServiceInfo`: real. `Serve(lis)`: grpc-go's own loop (temporary-error
backoff, `ErrServerStopped`), one goroutine per accepted connection: read the preface (else close),
read `GHead`; then, under `s.mu`, **refuse** (`GRefused`, close) if draining or `modelChoose()` (an
over-approximation of `MaxConcurrentStreams` and `GOAWAY`, `http2_server.go:552-557`), else mark
it **dispatched** (final). A dispatched stream gets a context with the incoming metadata (real
`metadata.NewIncomingContext`, with grpc-go's reserved keys added as `operateHeaders` adds them),
the peer (real `peer.NewContext` with the connection's addresses), the client's timeout
(`context.WithTimeout`), canceled by a reader goroutine on `GCancel`, an error or end of file; then
grpc-go's `handleStream` lookup (`Unimplemented` "unknown service"/"unknown method"), and for a
unary method one request (size check, the program's codec), the handler through the chained
interceptor, the reply marshaled (`MaxSendMsgSize`), `GTrailer` with the handler's status
(`status.FromError`, else `status.FromContextError`, `server.go:1461-1465`); for a streaming method
the handler with a `ServerStream` over the frames. **No `recover`**: a handler's panic is the
program's (grpc-go does not recover either). `GracefulStop`/`Stop`: grpc-go's `stop(graceful)`
(`server.go:1683`) with the transports replaced: close the listeners, wait for `Serve`'s goroutines,
then drain (undispatched streams refused) or close every connection, wait until none is left;
`GracefulStop` waits for the handlers, `Stop` does not (no `WaitForHandlers`).

**Client.** `NewClient(target, opts)`: the real `dialOptions` and target parsing; in place of the
balancer and subchannels, the resolver wrapper (it implements `resolver.ClientConn`: `UpdateState`
records the endpoints' addresses; `ParseServiceConfig` accepts exactly clientv3's round-robin config
and panics on any other, since a retry policy would change the model), every address reported
since the build, the idle state (the builder's `Build`, the program's `resolver/manual`, runs at
the first RPC; when no RPC is active the ClientConn may go idle, closing the resolver, and build
it again at the next RPC, as grpc-go's idleness manager does: the race of
`issues/etcd-client-resolver-build-race.md` stays reachable), the active streams, `closed`.
`Invoke` is grpc-go's own `invoke` (`call.go:69`) over the model's `newClientStream`; the chained
interceptors and per-RPC credentials are program code, called as grpc-go calls them (with
`RequireTransportSecurity` checked as grpc-go does). An **attempt**: pick any reported address
(`modelChooseN`), dial (the dial options' context dialer, else `(&net.Dialer{}).DialContext(ctx,
"tcp", addr)`), write the preface and `GHead` in one `Write`. **Transparent retry, only when
provably not dispatched**: the dial failed, the head did not get out whole (a failed write that
wrote less than all of it), or the server answered `GRefused`; then a new attempt on a fresh
connection, replaying the messages (and close-send) buffered since the stream began. Once a
header or a message is received the stream is **committed** (no `GRefused` can follow: the server
sends it only before dispatch). `WaitForReady(true)` (clientv3's default) keeps attempting until
the context is done; `false` fails fast with `Unavailable`. A transport failure (an error, or an
end of file before `GTrailer`) is an **own error**: the context's status if it is done
(`Canceled`/`DeadlineExceeded`), else any non-OK code (`modelChooseN`) with one of grpc-go's own
messages. Size limits (`MaxCallSendMsgSize`, `MaxCallRecvMsgSize`: `ResourceExhausted` with
grpc-go's text, the receive one checked on the frame's length), an unmarshal failure (`Internal`),
a second reply of a unary call (`Internal` "cardinality violation"), `Close` (every stream's
connection closed; later calls `ErrClientConnClosing`, `clientconn.go:70`), the `Peer`/`Header`/
`Trailer` call options (real `callInfo` and their `after`), as grpc-go. `NewStream` returns the
model's `clientStream` (one sender and one receiver may run concurrently, as grpc-go allows; a
mutex covers the connection swap of a retry and the writes); the generated code's generic wrappers
(`GenericClientStream[Req, Res]`, `stream_interfaces.go`) are real.

**Codecs at bytes** (as C4): the server calls its `CustomCodec` (etcd's `v3rpc/codec.go`:
`proto.Marshal`/`Unmarshal`, program code), the client grpc's `encoding/proto` codec, modelled as
`proto.Marshal`/`Unmarshal` of the message with its "not a `proto.Message`" error (grpc-go v1.84's
`CodecV2` with pooled buffers has the same results). Protobuf's trust is E2's alone; `msgsFit`
(`issues/grpc-codec-alloc-before-size-check.md`) moves to E2, where the allocation is.

**Status messages** travel as grpc-go sends them: the server encodes with grpc-go's own
`encodeGrpcMessage` and the client decodes with `decodeGrpcMessage` (real code from
`internal/transport/http_util.go`, translated), so a message arrives as grpc-go delivers it (each
invalid UTF-8 byte replaced), not by a trusted relation.

**What is kept from the documented semantics, and where:**

* *At most one dispatch per attempt*: a connection carries one stream, dispatched at most once
  (`dispatched` final under `s.mu`; refused ones never dispatched).
* *Transparent retry only if never dispatched*: the client's three cases above; never after a
  dispatched stream fails (no service-config retry policy: the round-robin config has none, and
  `stream.go:800-830` returns the error without one). More retries than grpc-go (any number, not
  only the first attempt, `stream.go:816`; no 256 KiB replay limit, `stream.go:1045`): U6.
* *`WaitForReady`, deadlines, cancellation*: above; the server's deadline is the client's
  timeout, and its context is also canceled whenever the connection fails.
* *`GracefulStop`/`Stop`*: grpc-go's `stop`, above.
* *Status codes and own messages*: handlers' statuses arrive as sent; own errors carry grpc-go's
  texts. **C5 (accepted)** is part of the model's faithfulness argument: no own message of grpc-go
  v1.84 equals an etcd error description or one of the two strings clientv3 resends mutations on
  ("there is no address available", "there is no connection available", `retry.go:93`), so the
  model's own messages (grpc-go's texts, a finite set in its code) classify as grpc-go's do; a
  script over the pinned grpc-go checks the claim (previous G10).

### 4.4 The net/http model

**Client** (sketch: `http_model_sketch.go`). `Transport.RoundTrip`: net/http's checks (nil URL or
header, missing host, an unsupported scheme, a `RegisterProtocol` alternative called instead;
`https` panics); `Proxy` is not consulted, since `ProxyFromEnvironment` never proxies a loopback
host (`httpproxy`'s `useProxy`, `vendor/golang.org/x/net/http/httpproxy/proxy.go:178-185`) and the
plan's addresses are loopback (a non-loopback plan would need the previous design's no-proxy
premise, its G12). An **attempt**: dial through the program's dialer (`DialContext`, else `Dial`,
else a `net.Dialer`; for rafthttp, etcd's timeout dialer), write the request line and `HHead` in one
`Write`, a goroutine copying the body (the program's `Body.Read`) into chunks, ending with `HEnd`
or `HAbort`, while the caller reads `HResp`; a context watcher closes the connection when the
request's context is done (the error is then `ctx.Err()`). The `*Response`: status, header, a body
over the chunks (`io.EOF` only at `HREnd`, `io.ErrUnexpectedEOF` if cut short; `Close` closes the
connection). **Resends** as net/http resends on a reused connection (`shouldRetryRequest`,
`transport.go:844`), each on a fresh connection, at the model's choice: nothing of the request went
out (`nothingWrittenError`) and the body is absent or rewindable (`GetBody`); or the request failed
before the response's first byte and `isReplayable` (`request.go:1561`: `GET`/`HEAD`/`OPTIONS`/
`TRACE` or an idempotency key, the body absent or rewindable). A failed dial is also resent (net/http
does not: an extra behavior). `CloseIdleConnections`: nothing to close. `Client.Do`/`Get`: net/http's
`send` through the client's transport (the program's or this one), `Timeout` as a context deadline,
errors wrapped in `*url.Error`; a `3xx` with `Location` panics (no redirect is followed: etcd's
handlers never redirect the paths its clients request; the mux's subtree redirect is for a bare
`/raft/stream`-style path no client sends).

**Server.** `Server.Serve(l)`/`http.Serve`: net/http's loop (temporary-error backoff,
`ErrServerClosed`), one goroutine per connection: the request line (an HTTP/2 preface, or a line
not ending in `HTTP/1.x`, closes it), `HHead`, then one request: `Method`, `URL{Path, RawQuery}`
(the client's `Path` and `RawQuery` sent as they are, which equals net/http's escape-and-parse
round trip for the paths etcd uses), `RequestURI`, `Proto`, `Header`, `Host`, `ContentLength`,
`RemoteAddr` (`c.RemoteAddr().String()`), a body over the chunks (`io.EOF` only at `HEnd`), a context
canceled when the connection fails or the handler returns; a `ResponseWriter` (`Header()`;
`WriteHeader`, the first wins; `Write`, with an implicit `200` and `Content-Type` sniffed by
net/http's own `DetectContentType` when unset; `Flush` through `http.Flusher`; the automatic headers
net/http adds, added the same way; no buffering: each `Write` one chunk). The handler (the program's:
`ServeMux`, rafthttp's, etcd's peer handlers) runs with **no `recover`** (net/http recovers and logs,
`server.go:1956`; the model makes a handler's panic the program's, which the proof must exclude:
true of the program once `issues/etcd-rafthttp-pipeline-process-error-panic.md` is fixed on the
fork). Then the head if not yet sent, `HREnd`, and the connection's `Close` (the program's wrapper).
`Shutdown(ctx)`: close the listeners, wait until no connection is active or `ctx` is done; `Close`:
close listeners and connections.

**Real code kept** (layer R): `Header` and `textproto.CanonicalMIMEHeaderKey`,
`NewRequest(WithContext)` (with `url.Parse` and the body type switch that sets `GetBody`),
`Request.WithContext`, `StatusText`, `DetectContentType`, `ServeMux` with Go 1.22's patterns (if
goose takes `routing_tree.go`/`mapping.go`'s generics; else a model of plain path patterns, the
previous C10), `http.Error` (real, if Perennial's `fmt` model covers its `Fprintln`; else patched
to the equivalent `Write`).

### 4.5 cmux's sniffing

cmux reads a new connection's first bytes through the base connection and replays them to the
matched listener. `cmux.HTTP2()` reads exactly HTTP/2's 24-byte client preface, which the grpc
model writes first; `cmux.HTTP1()` reads the first line and checks for `HTTP/1.x`, which the
net/http model's request line is; `cmux.Any()` reads nothing. These are the only matchers etcd uses
(`embed/serve.go:205-211`, `:278`, `embed/etcd.go:604`). The header-field matchers
(`HTTP2HeaderField*`, which parse HTTP/2 frames after the preface) would not match the models'
frames: not used by etcd, and a model of them would be stuck in the proof, not wrong at run time.
So the previous C6 (split the client port to avoid cmux) is not needed.

### 4.6 Faithfulness, in one place

The claim for each model: **every behavior of grpc-go (net/http) over Linux TCP, as the program
observes it** (which handlers run with which requests and contexts, what callers get back, which
program callbacks run: dialers, listeners, codecs, interceptors, credentials, resolvers, request
bodies), **is a behavior of the model over the TCP extension.** Not wire compatibility.

* *Over-approximations* (more behaviors): refusal of any undispatched stream; transparent retries
  beyond grpc-go's; any non-OK code on a transport failure; HTTP resends as if every connection
  were reused, and after failed dials; any reported address picked; idleness at any quiet moment;
  data visible at `Write` (no buffering, no flow control).
* *Invisible simplifications* (argued in each patch's docstrings): one stream or request per
  connection (only `RemoteAddr`/`peer.Addr` could tell, and they are any address), no HTTP/2
  framing, settings, pings, compression (etcd sets none), channelz, stats handlers (tracing off),
  binary logging, server workers.
* *Under-approximations* (panic, so the proof shows them unreached): section 4.1's list.
* *Exits*: grpc's `logger.Fatalf` checks (RegisterService) as panics or skipped (previous G8).
* *Previous gaps that are gone*: G2 (wrappers ran only on the preface: now on every byte), G3 for
  the transports' buffering (now T2), G5 (connection reuse: resends kept), G11 (header validation:
  real `Header` code), G12 for loopback.

## 5. The previous design's inventory, mapped; what becomes provable where

### 5.1 The previous extension's operations

| previous (`net-extensions-design.md` §4.1) | now |
|---|---|
| `Listen`, `Accept`, `LisClose`, `Dial`, raw `Write`/`Read`/`Close`/`Addr` | T's `Listen`, `Accept`, `Close`, `Dial`, `Write`, `Read`, `Check` (deadlines, socket options); addresses from the plan and the dial |
| `Nonce`, `ClaimD`, `ClaimA` (prefaces to find the base connection) | gone: the models read and write all bytes through the program's `net.Conn`s |
| `PutKV`, `GetKV` (headers, metadata, trailers) | fields of `HHead`/`HResp`/`GHead`/`GHeader`/`GTrailer`, built and read by M with R's `Header`/`metadata` |
| `HOpen`, `HStart`, `HBodyPut`, `HBodyEnd`, `HHead`, `HRespRead`, `HCancel` | the net/http client model (attempt, body copier, response body, context watcher) |
| `HTake`, `HBodyRead`, `HCommit`, `HWrite`, `HFinish`, `HGone` | the net/http server model (connection goroutine, request body, `ResponseWriter`, context) |
| `GOpen`, `GStart`, `GSend`, `GCloseSend`, `GCancel`, `GRecv` | the grpc client model (attempt, `clientStream`) |
| `GTake`, `GDrain`, `GSrvRecv`, `GSrvSend`, `GFinish`, `GGone` | the grpc server model (connection goroutine, refusal/dispatch under `s.mu`, `ServerStream`, drain in `stop`) |
| `GOwnErr` (any code, `grpcOwnMsg`) | the model's own errors (grpc-go's texts) with C5 in the faithfulness argument |
| `msgArrives` (status message relation) | real `encodeGrpcMessage`/`decodeGrpcMessage` |
| `Owner{node, epoch}`, takeover of a dead listener's record | the local fd table emptied by a crash; `Bindable` |

The ~95 Go functions of the previous §4.2 are now: ~20 in layer N (hand-written GooseLang), ~40
whose bodies the patches replace (the transports, servers, client connection, round tripper,
`Client.Do`, `Shutdown`), and the rest real code (option constructors, `invoke`, chaining, `status`,
`metadata`, `peer`, `resolver/manual`, `Header`, `NewRequest`, `StatusText`, `ServeMux`, ...).
The previous design's control server for joiners is not needed (crashreconf polls the member list).

### 5.2 Today's assumed specs, and the layer that proves them

| assumed today (E1, E7 of `trust-boundaries.md`) | becomes |
|---|---|
| `Spec/net/http/Listen.lean`, `Listener__Close.lean` (`net.Listen` and its listener) | theorems of N over T's specs |
| `Spec/net/http/Serve.lean` | a theorem of M (net/http server) |
| `NewRequest`, `Request__WithContext`, `Header__Get`/`Set`/`Get_owned`, `StatusText`, `URL__String`, `NewServeMux`, `ServeMux__Handle`, `Error` | theorems of R (real code), `Error` of M if patched |
| `Transport__CloseIdleConnections`; rafthttp's `NewRoundTripper`, `transport.NewTimeoutTransport` (names-only today) | M (`RoundTrip`, a no-op close), W over M and N |
| `Spec/net/http/Api.lean` (31 laws: `protoAt`, `addrFree`, `reserve`, `respW`, `readerAt`, request tickets) | definitions over T's `tcpProto`/pipes and M's frame protocol, laws as lemmas (a protocol prelude) |
| grpc `NewServer`, `Server__RegisterService`/`Serve`/`Stop`/`GracefulStop`, `NewClient`, `ClientConn__Invoke`/`NewStream`/`Close` | theorems of M (`Invoke` through real `invoke`), `ClientConn__Target` of R |
| grpc option constructors (`MaxRecvMsgSize`, `CustomCodec`, `Chain*Interceptor`, `KeepaliveParams`, `With*`, `WaitForReady`, `MaxCall*`, `Peer`, `StaticMethod`, `Creds`, `StatsHandler`) | theorems of R (real constructors over the real option structs); `Creds`/`StatsHandler` with non-nil arguments reach M's panics |
| `Server__ServeHTTP` | M panics: the spec becomes unreachability (TLS path not modelled) |
| `status/*`, `metadata/*`, `peer/*`, `credentials/insecure`, `health/*`, `health/grpc_health_v1/*`, `grpclog/SetLoggerV2` | theorems of R (status over E2's `spb.Status`) |
| `Spec/google_golang_org/grpc/Api.lean` (58 laws) and `peer/Api.lean` (6): `connAt`, `serves`, `addrAt`, `UnarySpec`, `StreamSpec`, `statusErr`, `sentStatus`, `ownErr`, `grpcMsg`, `outMD`, `dialOptAt`, `callOptOk`, `msgsFit` | definitions: `statusErr`, `outMD` in R; `connAt`, `serves`, `addrAt`, the contracts in M's protocol prelude; `grpcMsg` the model's finite own-message set; `msgsFit` moves to E2 |
| etcd's wrappers, cmux (names-only today) | theorems of W over N (a wrapper over a connection with protocol `P` is a connection with protocol `P`) |

**How the at-most-once claim is proved** (the protocol prelude's core, internal): a connection's
up-direction protocol says `GHead` carries nothing, each `GMsg` carries the resource its caller
attaches (for a unary call the contract `S md (norm c) Φ`), and the server's `GRefused` carries the
server's reader half `pipeR` of the up direction: a server that refuses has read only the head and
gives its right to read the rest back, so a client that reads `GRefused` reclaims every buffered
message's resource and can resend them on a new connection. A dispatched stream's reader half is
never given back, so its resources are consumed at most once (by the handler, or lost with a dead
server). A failed write that did not complete the head leaves the client its resources. HTTP: a
non-replayable request's resource is reclaimable only if nothing was written; a replayable one's
resource is persistent (duplicable), as today's boundary already says.

### 5.3 Consequences on the spec side

* **One protocol per address for the whole run, independent of the member hosted there.** With
  per-node crashes and peer-URL reuse across re-adds, slot `i`'s peer address serves every member
  incarnation the slot will host: its protocol must say what any of them answers (rafthttp's `412`
  on a mismatched `X-Raft-To`, `404`/`410` for a removed member, ...), or quantify over the
  incarnation that accepts the connection. To be settled with the protocol prelude (the previous
  design's §8 change, now forced).
* **Byte protocols under the contracts**: today's `Proto`/`AddrContract` vocabulary becomes a
  frame-level protocol over T's pipes; the client-facing statements need not change shape.
* `Http.addrFree`'s environment premise (one reserved string per socket) is replaced by the plan
  (T6, T7); `msgsFit` leaves grpc for E2; no per-generation laws (`protoFam_gen`, `addrFree_gen`).

## 6. Sizes and risks

| | previous design | this design |
|---|---|---|
| trusted semantics (Lean) | `Impl.lean` 575 lines, 39 operations over HTTP/gRPC records | `Impl.lean` 332 lines (draft), 7 TCP operations |
| trusted code, GooseLang | ~95 `TrustedCode` functions, 1500-2000 lines | `TrustedCode/net.lean` ~20 declarations, ~450 lines (`os.lean` is 433); 2 `modelChoose` hooks |
| trusted code, Go | none | grpc-go patch ~1800 lines, net/http patch ~1300 (each with a ~240-line framing copy) |
| real code translated, untrusted | grpc's `metadata`, `peer`, `codes`, `health`, stream wrappers; net/http helpers | the same, plus `status`, `resolver/manual`, option constructors and structs, `invoke`, chaining, `encodeGrpcMessage`, `NewRequest`, `textproto`, `url`, `DetectContentType`, `ServeMux` |
| extension Specs + Adequacy | ~2000 + 150 | ~900 + 150 (Grove's Specs: 538 for 10 operations) |
| proofs | TrustedCode ~6000, protocol prelude ~1500: ~10k | N ~800; framing library ~2000; grpc model ~6000; net/http model ~3500; real code R ~2500; prelude ~1500: ~17k |

The trusted text grows (about 2.3k lines before, of which 575 a bespoke semantics; about 3.9k now,
of which 332 a TCP semantics and 3.1k ordinary Go), but changes nature: the semantics is plain TCP,
justified against Linux in one table; the models are grpc-go's and net/http's own code with the
transports swapped, reviewable against them and runnable; and many statements that were trusted
(status, metadata, options, the request helpers) become verified real code.

**Risks:**

1. **Byte-level parsing in the proofs.** Encode/decode round trips (`u32`, strings, metadata built
   in a map's iteration order), `readFull`'s loop over partial reads, the framed-pipe ghost
   protocol (a frame's resource deposited at the `Write` that completes it; a frame cut by a failed
   write never completing, since the writer abandons the connection). Mitigation: one small
   framing file, proved once and reused for its copy (the two copies differ only in package names).
2. **Partial reads and writes** are confined to `readFull` and the one-`Write`-per-batch rule; the
   rest of the models see whole frames.
3. **Concurrency inside the transports.** grpc client stream: sender, receiver, context watcher, and
   a retry swapping the connection under a mutex; server: reader goroutine beside the handler,
   refusal/dispatch and drain under `s.mu` with a condition variable, `stop` waiting for
   connections; net/http: body copier beside the response reader, the context watcher, `Shutdown`'s
   connection tracking. Ordinary lock invariants, but many.
4. **Goose coverage** of the patched sources and of the reused real code: generics
   (`stream_interfaces.go`, `ServeMux`'s `mapping.go`), `reflect` (patched out), `fmt`
   (`http.Error`), `grpcsync`, atomics, timers. Each gap is patched (the trusted part grows) or left
   assumed for a while.
5. **Review load**: 3.1k lines of Go models to check against grpc-go and net/http, with section
   4.6's list as the checklist; the real-run tests catch vacuity, not over-claiming.
6. **The `net/http` patch is of the standard library**: goose must translate it from an overlay of
   the toolchain's source, and the real run needs `go -overlay`.
7. **Smaller than before**: the crash story (only the fd table), the extension's ghost state (no
   per-record ownership by incarnation), no preface claims.

## 7. Open choices

Marked **[user]** where they shape the trusted semantics or models, **[internal]** otherwise.

* **U1 [user]. How a node's crash reaches its peers.** (a) **Recommended**: no Perennial change;
  the crash empties the node's fd table, and peers see EOF (when caught up), errors or silence
  because the rules always allow them (T3). (b) A change to `DistLang`'s trusted definitions:
  an extension's crash relation may also change the global state, so the TCP crash would close the
  dead process's listeners (dials refused) and its connection ends (FIN or RST each), and EOF would
  need a FIN. More exact, but it changes Perennial's trusted semantics and its adequacy proof (each
  extension's crash interpretation gains a global obligation, and the TCP ghost state must let a
  crash rewrite records the dead generation owned), for no safety the proof needs.
* **U2 [user]. How the models are written.** (a) **Recommended**: Go, as patches of grpc-go v1.84.0
  and Go 1.27.3's `net/http` (4.1), with `modelChoose()` hooks as the only GooseLang. (b)
  Hand-written GooseLang `TrustedCode`, as `os`. (c) Shadow Go packages with only the reached API.
* **U3 [user]. One gRPC stream / one HTTP request per TCP connection.** (a) **Recommended** (4.2).
  (b) Multiplexed streams and pooled HTTP connections, closer to the real libraries: stream ids,
  per-connection demultiplexing goroutines, a pool, more proof, no behavior the program observes.
* **U4 [user]. The address plan** (the previous C3, kept): exact strings with their parsed
  `(ip, port)`, fixed for the run, `Listen` and `Dial` outside it stuck. **Recommended.**
* **U5 [user]. TCP over-approximations**: end of file whenever caught up, failures not sticky,
  deadlines untracked (any blocking operation may report one). **Recommended.** Alternatives: track
  per fd whether a deadline is set (so `ErrDeadlineExceeded` only there; one more bit and the
  setters as a recording operation); sticky end of file and resets.
* **U6 [user]. grpc's retry and error over-approximations**: retry any provably undispatched
  attempt any number of times; refuse any undispatched stream; any non-OK code with an own message
  on a transport failure. **Recommended.** Alternative: grpc-go's exact rules (first attempt only,
  the 256 KiB replay buffer, refusals only over `MaxConcurrentStreams` or when draining, codes per
  cause): more model, fewer behaviors, no safety gained.
* **U7 [user]. net/http's**: resends as if every connection were reused (and after failed dials);
  redirects panic; `Proxy` not consulted for the plan's loopback addresses. **Recommended.**
* **U8 [user]. C5** (accepted 2026-11-10) carried into the grpc model's faithfulness argument as
  described in 4.3, with the extraction script. Confirm the reading.
* **U9 [user]. Where**: this repository (`GooseLang/Ext/Tcp/`, `TrustedCode/net.lean`,
  `etc/model-patches/`), with the TCP extension proposed to Perennial later (the previous C7).
  **Recommended.**
* **U10 [user]. Real code or model for the borderline pieces** (`ServeMux`, `http.Error`, `status`,
  `health`, the generic stream wrappers): **recommended** real wherever goose takes it.
* **I1 [internal]. Handles**: integer fds in a per-node table, never reused within a process
  (settles the previous C11).
* **I2 [internal]. The framing's encoding** (`modelframe`): fixed 5-byte headers, length-prefixed
  fields, limits checked before allocation (grpc's message limits; 16 MiB headers, net/http's
  1 MiB `DefaultMaxHeaderBytes`).
* **I3 [internal]. The extension's ghost state** (2.7) and the protocol prelude's framed pipes,
  with `GRefused` carrying the server's read half (5.2).
* **I4 [internal]. Two copies of the framing** (a standard-library package cannot import a
  module), one proof.
* **I5 [internal]. Testing the models**: unit tests in each patched tree (refusal and resend paths
  forced through the `modelChoose` knob), and crashreconf's porcupine test run over the models
  (`replace` for grpc-go, `-overlay` for `net/http`) beside today's run over the real libraries.
* **I6 [internal]. Errors in Go's shapes** (`*OpError` over `os.SyscallError`, `ErrClosed`,
  `os.ErrDeadlineExceeded`), so that etcd's own error tests (`transport.IsClosedConnError`'s
  substring) behave as with Go.

The previous design's choices: C1 superseded (no prefaces), C2 moot (one extension, models as
code), C3 kept as U4, C4 kept (codecs at bytes), C5 kept (U8), C6 not needed (4.5), C7 kept as U9,
C8 kept (TLS panics), C9 replaced by U3/U7, C10 folded into U10, C11 settled by I1, C12 settled
(`status` is real code).
