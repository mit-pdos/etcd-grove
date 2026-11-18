# M2a: TCP as Go presents it (for review, 2026-11-12)

The trusted semantics of Go's `net` for the harness (design: `notes/harness-m2-netconn.md`, sections 1, 2, 3, 5).
Everything below typechecks against the pinned Perennial (`harness/lean/build.sh`, about 65 s); nothing is proved
yet except a few sanity examples. `safeDist_of_wp` is `sorry` (M2b).

## Files

| file | what |
|---|---|
| `harness/lean/Harness/GooseLang/Ext/NetConn/Impl.lean` | the extension `netConnExt` (name `"net"`): state, operations, outcomes. **The thing to review.** |
| `harness/lean/Harness/GooseLang/Ext/NetConn/Tests.lean` | five sanity examples (allowed and excluded outcomes), not trusted |
| `harness/lean/Harness/TrustedCode/net.lean` | the Go model of `net` over the extension: `Listen`, `Dial`, `DialTimeout`, `*TCPListener` and `*conn` methods, error values. **Also to review.** |
| `harness/lean/Harness/Code/net.toml` | goose configuration for Go's own `net` |
| `harness/lean/Harness/Code/net.lean`, `GeneratedProof/net.lean` | goose and proofgen output (generated) |
| `harness/lean/Harness/ManualProof/net.lean` | the empty module proofgen's output imports |
| `harness/lean/Harness/SafeDist.lean` | `Node`, `NodeStart`, `NetStart`, `SafeDist`, `safeDist_of_wp` (sorry) |
| `harness/netprobe/netprobe.go` (+ its `Code`/`GeneratedProof`) | the probe: an echo server and a client using `net` literally |
| `harness/netsem/` | the semantics examples, `run.sh` to measure them, `doc.go` with the results |
| `harness/lean/build.sh` | now also regenerates and typechecks the above |

## The semantics in plain words

State, shared by all nodes: the listeners (address, open or closed, connections dialed but not yet accepted) and the
connections. A connection has two ends (dialer, acceptor). Each end is open or closed and has a read and a write
deadline flag. Each direction is a byte stream: the bytes written and not yet read, and a status: live, fin (the
writer closed), cut (broken).

- **Listen(addr)** returns a new listener if no open listener has the same address string, or fails. Failure is always
  allowed.
- **Dial(addr)** fails (always allowed), or, if a listener is open on that exact string, makes a fresh connection and
  queues it at the listener.
- **Accept** returns any queued connection, not necessarily the oldest; or fails; or waits while none is queued. On a
  closed listener it fails.
- **Listener.Close** frees the address and drops the queued connections. A second Close fails.
- **Write(b)** appends the first k bytes of b and returns k. k is all of b when there is no error; with an error, k may
  be anything up to all of b (`WriteOutcome`). A short write comes with a timeout (only if a write deadline is set) or, on a broken connection, with an error. On a
  broken connection the bytes are thrown away, and the Write may still report success.
- **Read(buf)** returns 1 to len(buf) of the next bytes, in order, and no error. With nothing to read it waits while
  the stream is live; returns `io.EOF` if the peer closed; returns an error or `io.EOF` if the connection broke. With
  a read deadline set it may time out instead, whatever is buffered. `Read` of an empty buffer returns (0, nil).
- **Close** closes this end: the outgoing stream becomes fin (the peer reads the rest, then `io.EOF`). Every later
  operation on this end fails with "use of closed network connection". A second Close fails.
- **SetDeadline / SetReadDeadline / SetWriteDeadline** set or clear the flags (cleared by the zero `time.Time`).
  Time is not modeled: a set deadline may expire at any Read or Write. A timeout leaves the connection as it was.
- **A break** may happen at any Read, Write or Close of either end, before it takes effect: both streams become cut,
  and each loses an arbitrary suffix of its bytes (none, some, or all). After that each end learns of it on its own:
  a reader gets the surviving bytes, then an error or `io.EOF`; a writer's bytes are discarded, with success or an
  error.
- **Never**: bytes reordered, duplicated, corrupted, or delivered after a lost byte; a short write without an error;
  bytes and an error from one Read; a timeout without a deadline.
- **Start**: no listener, no connection (`NetState.empty`, `NetStart`).

Errors as Go code sees them: `io.EOF` unwrapped; everything else a `*net.OpError` with Go's `Op` ("read", "write",
"close", "set", "accept", "listen", "dial"), `Net` "tcp", Go's `Source`/`Addr`, and an `Err` whose `Timeout()` and
`Temporary()` are true/true for a deadline, false/false for a closed end, and arbitrary for a break or a failure.

## Choices, and why

1. **A break does not make every later operation on both ends fail** (the design note said it does). Measured on this
   host (`netsem/break_suffix.go`, `break_netns_test.go`): after a reset the reader still reads the bytes that had
   arrived (127973 of 2633835 written), then gets ECONNRESET, then `io.EOF` on the next Read; with the reset made by
   iptables, the other end's next three Writes all succeed. Linux keeps the receive queue on a reset and reports the
   reset once. A model in which both ends fail at once would exclude these runs, so it would be unsound. Instead the
   break cuts the streams, and each end finds out at its own pace.
2. **`io.EOF` is allowed after a break.** Measured (above). So `io.EOF` does not prove the peer closed cleanly;
   protocols must frame their messages (lengths), which our targets do.
3. **A timeout does not mean the connection is fine.** A dead connection reports ETIMEDOUT, whose `Timeout()` is true
   (Go's `Errno.Timeout`). The model gives breaks an arbitrary `Timeout()`. A deadline timeout itself leaves the
   connection usable (measured, `deadline_usable.go`), and a timed-out Write may have sent a prefix (measured: 2633835
   of 64 MiB), which a retry would follow with a new message, corrupting the framing. That is Go's behavior; the model
   keeps it.
4. **Breaks at Read, Write and Close only**, not at Dial, Accept, SetDeadline or Addr. A break is only observable
   through Reads and Writes, and a break can always be placed at the first operation that observes it: the bytes
   written in between are in the lost suffix.
5. **Waiting only where it is needed**: Read on an empty live stream, Accept with nothing queued. A Write never blocks
   in the model (the stream is unbounded). A real Write blocked by flow control, or anything blocked forever, is a
   prefix of a model run in which that thread is not scheduled, so safety is unaffected.
6. **Accept in any order**: a Dial returns before the server's kernel queues the connection, so two dials can be
   accepted in either order (`documented.go`).
7. **Address strings match literally.** This is only right in the claimed configuration: every node listens on
   "IP:port" with its own IP, and its peers dial the same string. `Listen(":8000")` on two nodes, or dialing an address
   spelled differently from the listener's, is outside the model (`documented.go`, AddressSpelling). The kits generate
   the addresses; the rig gives each node its own IP.
8. **Close with unread input** resets the connection in Linux (measured: the peer read the 17 bytes, then ECONNRESET).
   The model needs nothing extra: the reset is a break at the peer's next operation.
9. **Listener.Close drops queued connections**; their dialers see a reset (measured), again a break.
10. **Failures are always allowed** for Listen, Dial and Accept (in use, refused, backlog full, out of file
    descriptors). Close of an open end never fails (Linux's close of a TCP socket returns 0).
11. **Deadlines are flags, not times.** No clock is modeled; a set deadline may expire at any time, a cleared one never.
    "Cleared" means equal to the zero `time.Time` (a `Time` with the zero instant and another location counts as set,
    which only allows more timeouts).
12. **The Go model's values.** `Conn` is a real `*TCPConn` (so `conn.(*net.TCPConn)` works), with real promoted
    methods. The inner error is a model-only type `net#model.connError` (no Go type can have that name), not Go's
    `*os.SyscallError` or `poll`'s deadline error; the difference is visible only through `os`, `syscall` or
    `internal/poll` values, which no lab proof can use today. `Error()` strings and `TCPAddr.String()` are arbitrary
    (code that greps error messages, a common idiom, stays sound). Addresses are arbitrary `*TCPAddr`s, fixed per
    socket (Go returns the same pointer every time).
13. **`net`'s package variables** have trusted initializers that do nothing, so any use of them (`net.ErrClosed`,
    `net.IPv4zero`) is stuck, i.e. unprovable rather than wrong. Go's initializers only allocate values the subset does
    not use.
14. **Ids, not opaque values.** Sockets are `w64` ids in unexported `netFD` fields (Go code cannot forge them), as
    etcd-grove's file extension uses fds; the extension needs no value type. A call with an unknown id is stuck.
15. **The statement is at the extension list `[netConnExt]` and needs no ghost state** (`SafeDist`, `NetStart` are
    stated on the semantics only). A node is its package's `Assumptions` (for a kit: the generated `Assumptions` and
    `net.model.Assumptions`), `initialize'` and `main`; its start is "a Go context meeting its assumptions, no package
    initialized, one thread". The conclusion at each node is `Dsv.Ok` (the single-node statement's).
    `safeDist_of_wp` is stated over any `ExtInterp netConnExt` whose start predicates accept the empty network, with
    `goose_dist_adequacy`'s obligation as the premise; M2b replaces `extsGlobalStart` by the real start resources.

## What Goose needed

- `net.Conn` as an interface translates with no gap. So do `Listener`, `Error`, `Addr`, `conn`, `TCPConn`, `OpError`,
  `TCPAddr`, `IP`. Method calls on a `net.Conn` are ordinary interface dispatch to `*TCPConn`.
- Goose is run on Go's own `net` with `Code/net.toml` (`translate` a dozen names, `trusted` the socket layouts, the
  subset's functions and methods, and all 66 package variables), `-lean-root net=Harness`, and `CGO_ENABLED=0` (else
  the cgo resolver adds 9 more variables). Everything else in `net` is names-only.
- **Gotcha:** goose emits the `MethodUnfold` of a promoted method (`*TCPConn`'s `Read`, from `conn`) only if
  `TCPConn.Read` is not axiomatized, so those names must be in `translate` although `TCPConn` declares no such method.
- Trusted types (`netFD`, `TCPListener`) get no field facts from goose; `net.model.Assumptions` states them by hand (as
  etcd-grove's `os.file.FieldAssumptions`), together with the model-only error type's method table. proofgen also
  emits no `TypedPointsto` instances for them: M2b writes those.
- proofgen's `GeneratedProof/net.lean` has 140 `sorry -- axiomatized type` instances for the names-only types, as
  Perennial's own `GeneratedProof/os.lean` has. They are never used by the subset, but the gates should check that no
  result's axioms include `sorryAx`.
- **`time.Now` is not a gap** (corrected in M2b; this bullet first said it was names-only). The pinned Perennial
  translates `time` and gives `time.Now` a spec at its trust boundary: `time.Now.spec` (`Perennial/Spec/time/Now.lean`:
  some `time.Time`, nothing else), assumed as the axiom `time.Now.wp_proof` (`Perennial/Proof/time/Now.lean`, because
  `Now` reads the clock through a `go:linkname`) and linked as `time.wp_Now` (`Perennial/Proof/time/Link.lean`).
  `Time.Add` is translated and proved (`time.Time.Add.wp_proof`, `Time.wp_ptr_Add` in `Results.lean`). So
  `conn.SetDeadline(time.Now().Add(d))` is provable as it is; a proof that uses it adds `time.Now.wp_proof` to its
  axioms, as etcd-grove's do.

## For etcd-grove

The extension follows etcd-grove's conventions: name `"net"` (the Go package), `GooseLang/Ext/NetConn/Impl.lean`,
`TrustedCode/net.lean` with `X.impl` models citing Go's source, `Code/net.toml`, model-only names with `#`, a semantics
examples package with a claimed configuration (theirs is also Linux 7.0 and Go 1.27.3). `Impl.lean` imports only
Perennial; `TrustedCode/net.lean` imports Perennial and `Impl`; nothing depends on the harness's other modules. To
adopt it, etcd-grove would copy those three files and `netsem/`, add `net` to its goose projects with the toml, and take
M2b's `Specs.lean`.

grpc-go sits on `net`, but etcd-grove's grpc model is trusted at grpc's API (`Server.Serve`, `ClientConn.Invoke`) and
does not look below it. This extension could later sit under it in two steps: first, `Serve(lis)` would receive a real
model listener (from `net.Listen`) and its `acceptRun` leaf would be restated to accept from the extension's listener,
so both models share one network state; second, much later, grpc's transport (HTTP/2 framing over `net.Conn`) could be
translated and proved over this extension instead of trusted. Neither is needed for etcd-grove's present results.

## Open questions

1. **Choice 1** (a break does not fail both ends at once) changes the design note. Agree?
2. **Crashes (phase 3)**: Perennial's crash keeps the global state, so a crashed node's listener stays open and its
   restart can never listen on its address again. That is unsound for crash runs. Proposal: give each node an identity
   and an incarnation in the extension's local state (bumped by `crash`), record the owner in each listener and
   connection end, and let `Listen` take over an address whose owner is an older incarnation of the same node (peers'
   connections to it then see breaks, which the model already allows). No Perennial change needed.
3. **`time.Now`** (above): fix in Perennial, or carry a lab-side `time` model?
4. **`net.ErrClosed`** is unprovable to use (`errors.Is(err, net.ErrClosed)`, common in servers to stop an accept
   loop). Translate `ErrClosed` and the `internal/poll` error it names, or model it?
5. **Address spelling** is a deployment assumption. Should `SafeDist` take the node addresses as data and state it
   (every `Listen`/`Dial` argument in a given set of "IP:port" strings)? Today it is only in the docstrings and
   `netsem/documented.go`.
6. **Unmeasured claims**: accept order and ETIMEDOUT are documented, not measured; the rig's veth links are not
   measured yet (M2e). Fine to leave to M2e?

## Decisions (2026-11-13, the user and the lab)

- **The extension stays a new one, on Grove's structure** (the user: option 1). Perennial's two network extensions
  do not model `net.Conn`: `Ext/Net` is a datagram set per address, `Ext/Grove`'s connections are message sets
  (reorder, duplication, whole messages, no close, EOF or deadlines). Building `net.Conn` as model code over either
  would trust the model code to cover every TCP behavior anyway, with more proof work.
- **Choice 1 accepted:** a break cuts both directions, each losing a suffix, each end finding out at its own pace
  (measured).
- **`time.Now`: no gap.** The pinned Perennial already has its trust-boundary spec (`time.Now.wp_proof`,
  `Perennial/Proof/time/Now.lean`: some time, nothing else), as etcd-grove uses; `Time.Add` has a spec too. This note's
  "What Goose needed" was wrong on this point.
- **`net.ErrClosed`:** modeled (neither Perennial nor etcd-grove gives `errors.Is(err, net.ErrClosed)` a meaning;
  etcd-grove has only its untranslated initializer).
- **Addresses:** `SafeDist` takes the node addresses as data and states the spelling assumption as a premise.
- **Crashes:** phase 3, with the proposal above (node identity and incarnation in the local state).
- **Unmeasured claims** (accept order, ETIMEDOUT, the rig's veth links): measured on the rig during M2b.

## M2b result (2026-11-13)

Everything below typechecks against the pinned Perennial with no `sorry` (`harness/lean/build.sh`). Nothing in
Perennial was changed.

### What was proved

- **The extension's ghost state and specs** (`harness/lean/Harness/GooseLang/Ext/NetConn/Specs.lean`): the instance
  `netConn_interp : ExtInterp netConnExt` (ghost state, state interpretation `netCtx`, start resources `netStart`, their
  allocation `net_global_init`), and a Hoare triple for each operation: `wp_Listen`, `wp_CloseListener`, `wp_Dial`,
  `wp_Accept`, `wp_Read`, `wp_Write`, `wp_Close`, `wp_SetDeadline`; plus `addr_set_proto` (fix an address's two
  protocols, once), `recvTok_proto` (what was read meets the protocol) and `sendTok_sentLb` (what was written, as a
  persistent fact for the peer). The waiting steps of `Read` and `Accept` are handled once, by Löb induction, in
  `wp_netOp`.
- **The bridge** `safeDist_of_wp` (`harness/lean/Harness/SafeDist.lean`), from `goose_dist_adequacy`, as DsvNet's
  `safeNet_of_wp` is from `goose_adequacy`: a fixed `BundledGFunctors` (`netDistGF`, Perennial's slots plus one `AllG`
  slot) with its `GooseGpreS`; the start predicate discharged from the configuration (no listener, no connection,
  distinct addresses); the step and thread bounds `n + 1` and `n + 2`, with `DistThreadsBelow.of_single`.
- **The Go model's functions** (`harness/lean/Harness/Spec/net/<fn>.lean`, `Proof/net/<fn>.lean`, etcd-grove's
  layout; shared definitions in `Proof/net/Base.lean`): `net.Listen`, `Dial`, `DialTimeout`, `(*TCPListener).Accept`,
  `Close`, `Addr`, `(*TCPConn).Read`, `Write`, `Close`, `SetDeadline`, `SetReadDeadline`, `SetWriteDeadline`,
  `LocalAddr`, `RemoteAddr`, each `<fn>.wp_proof : <fn>.spec` from the extension's specs, and `net.initialize'.wp_proof`
  (given `time`'s and `io`'s initializer specs; it gives `isPkgInit pkg_id.net`, which holds the persistent value of
  `net.ErrClosed`). `Base.lean` adds the `TypedPointsto`/`IntoValTyped` instances proofgen did not emit (`netFD`,
  `TCPListener`, the model-only `connError`) and the representation predicates `ownTCPConn c cid side` and
  `ownListener l lid a` (persistent). The specs mirror the extension's: Listen takes `addrTok a`; Dial and Accept take
  `addrProto a P Q` and return, on success, a `*TCPConn` in a `net.Conn` with `ownTCPConn` and `connEnd` (with the
  protocols swapped for Accept); Read and Write carry `recvTok`/`sendTok` and the buffer's points-to; every error
  result is `nil` exactly when the extension's code is success, `io.EOF` for EOF, and otherwise a `*OpError` whose
  `Err` is the model's `ErrNetClosing` when the code is "closed". A call through the `net.Conn`/`net.Listener`
  interface steps to the concrete method, so the concrete specs serve (checked on `Close`). The network argument must
  be the literal `"tcp"`.

### The spec shape, and why

Mono-list/SPSC style, after Perennial's SPSC channel and etcd-grove's gRPC stream spec. Each direction of a connection
is a stream with a writer and a reader. The writer owns half of a mono-list of all bytes it has written (`sendTok cid
side P W`); the reader owns half of a ghost variable of all bytes it has read (`recvTok cid side P R`); the state
interpretation owns the other halves and relates them to the model's stream: the bytes in flight are `W` minus `R`
while the stream is live or finished, a prefix of that once it is cut. Each direction has a user predicate on
prefixes, `P : w64 → List w8 → IProp` (a saved predicate), fixed per address by `addrProto a P Q` (`P` for what
dialers write, `Q` for what acceptors write): a `Write` of `bs` requires `□ P cid (W ++ bs)`, and a reader learns `□ P
cid ext` for some extension `ext` of what it has read. A framing proof states `P` as "an encoding of messages, each
satisfying Φ".

- Address tokens from the start: `globalStart` gives, for each configured address, `addrTok a` and `addrUnset a`;
  `Listen` consumes the token and the listener's `Close` gives it back (the caller frames it).
- `Dial` gives the dialer's end (`connEnd cid false P Q [] []`); the acceptor's end (`connEnd cid true Q P [] []`)
  waits in the state interpretation, in the listener's pending list, until `Accept` hands it over. So the dialer and
  the acceptor get the two ends of the same connection, with the protocols swapped.
- Breaks, timeouts, closed ends and EOF are error results: a reader's error leaves `R` unchanged; a writer's `W` grows
  by what `Write` reports, whether or not the bytes survive a break. The specs do not distinguish the errors: a
  protocol cannot rely on `io.EOF`, which may also follow a break.
- `Close` and the deadline setters need only the persistent `isConnP cid`; a third goroutine can close a connection
  that two others read and write.

Hoare triples, not `atomic_wp`: every resource an operation changes is owned by its caller (the writer's mono-list
half, the reader's ghost-variable half, the address token) or is persistent, and everything shared is in the state
interpretation. No operation needs to open a client invariant at its linearization point. A client that shares an end
between goroutines puts `sendTok` or `recvTok` in a lock invariant, as with any owned resource. `Read` needs the
credit-carrying instance (`GooseGlobalGS .hasLC`), to strip the later of the saved predicate's agreement.

### Axioms

`build.sh` prints them (`harness/lean/Axioms.lean`, section M2b). The extension's specs, `net_global_init` and
`safeDist_of_wp` depend on Lean's three only (`propext`, `Classical.choice`, `Quot.sound`): the extension is
definitions, not axioms, so the trusted model adds nothing to the list; it is trusted by review. The Go model's specs add only goose's names-only declarations of `net`
(`net.X`, `X.underlying`, `X.zero_val`, and a few of `sync` and `internal/synctest`), as every proof over a goose
package with axiomatized types does; no `sorryAx` (the 140 sorried instances in `GeneratedProof/net.lean` are not
used). A client that uses `time.Now` adds Perennial's `time.Now.wp_proof`.

### Model changes, each with its semantics example

1. **Configured addresses** (`Impl.lean`: `NetState.addrs`; `Listen` and `Dial` on any other string are stuck). This
   makes the spelling assumption checkable: a safety proof now also proves that every `Listen`/`Dial` argument is one
   of the configured strings. `SafeDist nodes cfg` takes the configuration as data (`NetConfig`: node `i`'s IPv4
   address, and the endpoints) and states `NetConfig.WellFormed` as a conjunct: one IP per node, distinct, ordinary
   unicast (not 0/8, 127/8 or 224/4 and up), every endpoint on one of them with a port in 1..65535, spelled
   canonically (`Endpoint.spell`: decimal without leading zeros), no address twice. It is decidable; a kit proves it
   by `decide` (an example in `SafeDist.lean`). Example: `netsem/documented.go`, AddressSpelling (assumed of the
   deployment; the rig gives each node its own IP).
2. **`net.ErrClosed`** (`TrustedCode/net.lean`: `ErrClosed.init`, `model.codeErr`). The initializer allocates one
   model-only error `&connError{false, false}` (the model's `poll.ErrNetClosing`, in the model-only variable
   `net#model.errNetClosing`) and sets `net.ErrClosed` to it; `codeErr` returns that pointer for a closed end and a
   fresh pointer for every other error. `errors.Is` (translated, comparing pointers and unwrapping the `*OpError`
   through its translated `Unwrap`) is then true exactly for the closed-end errors. Example: `netsem/err_closed.go`,
   measured: true, with `Timeout()`/`Temporary()` false, for Read, Write, SetDeadline and a second Close on one's own
   closed connection, a Read blocked when another goroutine closes it, Accept (blocked or later) and a second Close on a
   closed listener; false for EOF, a timeout, ECONNRESET, EADDRINUSE and ECONNREFUSED. A program that assigns
   `net.ErrClosed` changes only the variable, as in Go; the specs, however, give `net.ErrClosed` as a persistent
   (read-only) points-to, so such a program is not provable.

### Measurements (the rig's namespaces and veth links; `harness/netsem/doc.go`)

Reproduce with `harness/netsem/run.sh` (about 35 s) and `harness/netsem/run-veth.sh`; the host's network was checked
unchanged after each run.

- **Accept order** (AcceptAnyOrder): accepted out of order 1000 of 1000 times when node 0's link has 5 ms of delay and
  node 2 dials after node 0's `Dial` returned; 71 to 157 of 1000 with concurrent dials (three runs, one with jitter);
  0 of 1000 for back-to-back dials from one node. The model's "Accept returns any pending connection" is needed.
- **ETIMEDOUT on a dead connection** (TimeoutOnBreak): with a partition, a blocked `Read` returns "connection timed
  out" after 2.3 s (TCP_USER_TIMEOUT 2 s), 3.1 s (keep-alive) or 3.2 s (tcp_retries2=3): `errors.Is(err,
  syscall.ETIMEDOUT)`, `Timeout()` true, `Temporary()` true, not `os.ErrDeadlineExceeded`; then EOF, EOF; Writes
  return EPIPE; the peer, once the partition is lifted, writes successfully, then reads 0 bytes, ECONNRESET, EOF. This is a break with an arbitrary
  `Timeout()`, which the model has, and it is why `Timeout()` of a break is arbitrary.
- **veth versus loopback**: the same outcomes in every example; only the counts differ (a partial write of 796400
  bytes on veth against 2633835 on loopback; 125336 bytes read before the reset against 127973).

### Open questions

1. **Upstream to Perennial**: `monoList_halves`/`monoList_halves_update` (a mono-list split into two halves and
   updated with both), `box_eq_rewrite` (rewrite under `□` with an internal equality), and the `wp_netOp` pattern (a
   blocking extension operation's Löb loop, with a persistent progress obligation) are general. They live in
   `Specs.lean` for now.
2. **Error kinds in the specs**: the specs give no way to tell EOF from a break. A protocol that wants "the peer closed
   cleanly" cannot have it (TCP cannot give it either, after a break); `errors.Is(err, net.ErrClosed)` is meaningful at
   the Go level, where `codeErr` distinguishes it.
3. **Crashes (phase 3)**: unchanged; the proposal in "Open questions" above still stands.
4. **Error kinds at the Go level**: the extension's specs return some failure code, so the Go specs quantify it; a
   client cannot conclude `errors.Is(err, net.ErrClosed)` from having closed a listener (an accept loop that stops on
   it must treat any error as possibly final). Strengthening `wp_Accept`/`wp_Read` to say "closed end gives the closed
   code" needs the closed state in the ghost state (a closed-end token); not done. No spec of `errors.Is` itself is used.
5. **The probe's accept loop** was not sketched (M2c); the interface-dispatch check above is the only usability check of
   the Go specs so far.
6. **Subnet broadcast**: `WellFormed` excludes the limited broadcast and multicast but not a subnet's broadcast
   address (it depends on the netmask). The rig's /24 never assigns .255; a kit should not either.

## M2c result (2026-11-13)

The probe is proved end to end: `netprobe_safeDist : SafeDist [clientNode, serverNode] probeCfg`
(`harness/lean/Harness/Proof/dsverify_lab/harness/netprobe/Results.lean`), with no `sorry`, typechecked by
`harness/lean/build.sh` (exit 0, about 2 minutes; `./build.sh regen` re-runs goose first). Nothing in Perennial was
changed; `Impl.lean` and `TrustedCode/net.lean` are unchanged.

### The probe

`harness/netprobe/netprobe.go` (109 lines, 82 without comments and blank lines), rewritten in the targets' style:
`ServerMain` listens on the constant `ServerAddr` ("10.77.0.11:7000", node 1 under the rig), accepts in a loop, and
echoes each connection in its own goroutine (read into a 64-byte buffer, write back `buf[:n]`, close on any error);
`ClientMain` dials with `DialTimeout`, sets the write deadline (`time.Now().Add(time.Second)`), writes `Msg` ("hello,
echo"), sets the read deadline, reads until it has `len(msg)` bytes or an error (partial reads appended), closes, and
`check`s the echo: it panics unless what came back is a prefix of what it wrote. So the theorem says the echo is never
longer than the message or different from it, whatever the network does in the model; a proof of "no panic in net
calls" alone would not do. Dropped from M2a's probe: `Dial`, `SetDeadline`, `LocalAddr`/`RemoteAddr`, `Listener.Addr`,
the `net.Error` type assertion and the `io.EOF` comparison (still translated in `net`, specified in M2b, unused here).
`cmd/client`, `cmd/server` and `rig.toml` run it under the rig: PASS (client exit 0, "echo checked"); a broken server
(`buf[0]++` before the echo, in a scratch copy) FAILs with "netprobe: echo differs from the message".

### What was proved

- `wp_check`, `wp_Ping`, `wp_ClientMain` (`Client.lean`); `wp_echo`, `wp_Serve`, `wp_ServerMain` (`Server.lean`), from
  the M2b specs of `net`'s functions (`Proof/net/*`), `time.wp_Now`, `time.Time.wp_Add` and Perennial's slice specs.
  The protocol of the one address (`echoProto`, `Base.lean`), in both directions: what is written is a prefix of
  `msg`. The client writes `msg`; the server's reader learns (`recvTok_proto`) that what it read is a prefix of `msg`,
  which is what its write needs; the client's reader learns the same of the echo, which is what `check` needs. The
  echo loop's invariant is just the two tokens with equal `W` and `R`.
- `wp_initialize'`, `wp_boot_client`, `wp_boot_server`, and `netprobe_safeDist` (`Results.lean`): `safeDist_of_wp`; in
  its start update the address's protocols are set (`addr_set_proto`), the token goes to the server node, the
  persistent `addrProto` to both. `probeCfg` is the rig's (node `i` at 10.77.0.(10+i); WellFormed by `decide`).
- New in `SafeDist.lean`: `nodeWp_of_boot`, a node's `nodeWp` from a WP of its boot program under any local ghost
  state, the Go semantics and assumptions its `NodeStart` gives, and `ownGoState ∅` (generic; the kits need it).

### Axioms

`netprobe_safeDist`: Lean's three; goose's names-only declarations of `net` (68 types with their `underlying` and
`zero_val`), of `sync` (`Map`, `poolChainElt`) and `internal/synctest` (`CurrentBubble`, `OtherBubble`, `Unbubbled`), as
in M2b; and Perennial's trust-boundary spec `time.Now.wp_proof` (the client sets deadlines from `time.Now`). No
`sorryAx`. `build.sh` prints them (`Axioms.lean`, section M2c).

### Line counts

Go: `netprobe.go` 109 (82 code). Lean (without comments and blank lines): `Base.lean` 50, `Client.lean` 199,
`Server.lean` 145, `Results.lean` 168 (of which `nodeWp_of_boot`, 20, moved to `SafeDist.lean`); about 540 in all, for
82 lines of Go. Changed M2b files: `Spec/net/TCPConn__Read.lean` (1 line), `Proof/net/TCPConn__Read.lean` (+40).

### Frictions, and recommendations

1. **`Read`'s count was too weak (spec changed).** M2b's `Read` spec gave `sint.nat n = data.length`, which a negative
   `n` also meets when nothing is read; a caller that slices `buf[:n]` (both loops here, and `readFull`'s `n += k`
   in the Paxos kit) then cannot exclude the slice panic. The spec now says `n = W64 data.length`, as `Write`'s does.
   The cause is Perennial's `wp_slice_copy` (`sint.nat n = min ...` only); the proof covers the empty case with
   `wp_slice_copy_of_len_zero` and the rest by `0 < sint.nat n`. Recommend upstream: `wp_slice_copy` returning `n =
   W64 (min ...)`.
2. **Error results are awkward to case on.** Every `if err != nil` needs `rcases err with ei | _`, and for `Listen`,
   `Dial` and `Accept` the spec's `err ≠ interface.nil` has to be turned into `∃ i, err = interface.ok i` by hand
   (four times). `Write`'s "no error means everything written" takes two conjuncts (`err = nil ↔ code = errNone`,
   `code = errNone → k = len`). Recommend: state the Go specs' error conditions on `err` directly (`err =
   interface.nil → k = bs.length`; failures as `∃ i, err = interface.ok i`), keeping `code` only where the error's
   kind is described (`connErr`).
3. **Buffer slicing after a `Read`** is 20 lines, twice: `ownSlice_split_all` at `n`, the arithmetic `sint.Z (W64
   |data|) = |data|`, then `ownSlice_combine` and `ownSlice_trivial_slice_2` to put the buffer back. Recommend a
   derived spec (`Read` giving `slice.slice b 0 n ↦* data` and the rest) or a lemma for "split a slice at a length
   below 2^63". Also: Perennial's `word` once produced a proof the kernel rejected (with list-length hypotheses in
   context; clearing them fixed it).
4. **Protocol facts.** `recvTok_proto` gives `protoPrefix` (`R = [] ∨ ∃ ext, R ≼ ext ∗ □ P cid ext`); for a
   prefix-closed `P` that is just `P cid R`, which needed a 5-line lemma (`protoPrefix_echo`). Recommend a library
   lemma for prefix-closed protocols. Framed protocols (the kits) are prefix-closed only as "whole frames then a frame
   prefix", which is the form they need anyway (a short write leaves a frame prefix).
5. **M2b's open questions 2 and 4 (an error's kind; is it final?) did not bite.** Safety of an accept loop needs
   only what `Accept` requires, all persistent (`ownListener`, `addrProto`); the probe's loop stops on any error, and a
   loop that retries after errors (the Paxos kit's) has the same invariant. Distinguishing `ErrClosed` or EOF would
   matter only for a proof that relies on the loop ending or the peer closing cleanly (none here). `Listen` returns the
   token in both cases, so a retrying `serve` (the Paxos kit's) is also fine.
6. **Interface dispatch needs nothing.** `wp_auto` steps a call through `net.Conn`/`net.Listener` holding
   `interface.mkOk (*TCPConn) #c` to the concrete method, and the concrete specs apply (Read, Write, Close,
   SetReadDeadline, SetWriteDeadline, Accept, listener Close).
7. **Node plumbing.** From `nodeWp` to a node's WP needs `nodeWp_of_boot` (now in `SafeDist.lean`): destructure the
   local ghost state to move the Go semantics along `goose_go_local_context = σ.goState.goLctx`, then
   `ownGoState ∅`; plus the usual `getIsPkgInit` table of transitive imports per boot program (9 packages here).
   The start resources of `safeDist_of_wp` (`addrTokG netDistGS a`) and the specs' (`addrTok a`) unify as they are.
   Recommend for many nodes: a lemma giving the `[∗list]` over `zipWith` from per-index facts (the probe matched
   `σs` against a two-element list), and one setting every address's protocols at once.
8. Small: `time.Second` is a reducible `val`, so `Time.wp_Add` needs the duration spelled (`W64 1000000000`).

### What the Paxos kit's proof will need beyond the probe

The probe exercised `net.Listen`, `Listener.Accept` (through the interface), `net.DialTimeout`, and `Conn` `Read`,
`Write`, `Close`, `SetReadDeadline`, `SetWriteDeadline`, all of the kit's `net` surface (kits/paxos-m2/README.md). Beyond
it (from `tcpnet.go` in the fork):

- **Several addresses and nodes**: six configured addresses, every node listening on its own and dialing the others;
  the start update sets each address's protocols and gives each node its token (lemmas of item 7).
- **A framed protocol with ghost content**: `P` for an acceptor's address = "a sequence of frames, each the
  length-prefixed encoding of a message to an acceptor satisfying the Paxos invariant's per-message fact (persistent
  ghost facts), then a prefix of one frame"; `Q` = nothing (connections are one-way). Lemmas: decoding the complete
  frames of a prefix of such a sequence (length prefixes fix the boundaries), with `marshal.ReadInt`/`WriteInt`/
  `WriteBytes`; `readFull`'s loop reads into `buf[n:]` (an offset slice, item 3) and `readFrame` reads a header then a
  body, so its invariant is "`R` is whole frames, then this frame's prefix".
- **Connections in a map, writes that may fail**: `tcpNetwork.conns` (map from agent to `net.Conn`) owns each
  connection's `sendTok` with `W` = whole frames; after a failed `writeFrame` the connection is closed and dropped, so
  its token (with a frame prefix in `W`) is never used again, which is what the framed `P` requires. The reader side
  (`readLoop`, a goroutine per accepted connection) owns `recvTok`; deliveries go through channels (Perennial's
  channel specs, as in M1's mux).
- **Liveness-free retries**: `serve` retries `Listen` with `time.Sleep`; `acceptLoop` sleeps and continues on errors
  (item 5: fine for safety); `send` re-dials on failure (each `DialTimeout` gives fresh ends with empty `W`/`R`).
- Not needed by the kit: `Dial`, `SetDeadline`, the address getters, `Listener.Close`, `io.EOF`, `net.Error`,
  `net.ErrClosed`.

## Ergonomics pass (2026-11-13)

M2c's frictions 2, 3, 4, 7 and 8, before the first `net` kit (paxos-m2). `Impl.lean` and
`TrustedCode/net.lean` are unchanged; `build.sh` builds everything with no `sorry` (M1's results
included); the new lemmas depend on Lean's three axioms only (`Axioms.lean`).

**Specs (friction 2): error results stated on `err`.** The meaning of each spec is unchanged:
- `Listen`, `Dial`/`DialTimeout`, `Accept` (`Spec/net/Listen.lean`, `newConnResult` in
  `Proof/net/Base.lean`): the failure disjunct is `∃ i, ⌜v = interface.nil ∧ err = interface.ok i⌝
  ∗ ∃ code, ...`. Before, the disjunct said `err ≠ interface.nil`, and every caller turned that into
  `interface.ok i` by hand.
- `Write`: `err = interface.nil → k = bs.length`, replacing `code = errNone → k = ...`.
- `Read`: `(err = interface.nil ↔ code = errNone) ∧ (err ≠ interface.nil → data = []) ∧ (err =
  interface.nil → bs ≠ [] → data ≠ [])`.

The proofs of the five specs changed by a line or two each.

**New library: `Harness/NetLib.lean`.**
- **Friction 3:** `ownSlice_take_acc b dq data rest`. From `b ↦*{dq} (data ++ rest)` it gives:
  - the bounds of `b[:len data]`, and `sint.Z`/`sint.nat (W64 len data) = len data`;
  - `slice.slice b 0 len ↦*{dq} data`;
  - the wand back to `b`.

  This is the split after a `Read`, which took 20 lines before. With the `Read` spec's `n = W64
  (length data)`, a `buf[:n]` is one `iapply` plus `ite_eq_left`. I did not add a derived `Read`
  spec: the lemma serves `buf[n:]`-style offsets too (paxos's `readFull`).
- **Friction 4:**
  - `ProtoPrefixClosed P` is a structure: `P cid []` holds, and `P` is closed under prefixes.
  - `ProtoPrefixClosed.of_pure` builds one for a pure protocol.
  - `protoPrefix_closed` and `recvTok_proto_closed hP` give `recvTok ... ⊢ recvTok ... ∗ □ P cid R`.
- **Friction 8:** needed nothing. `time.Time.wp_Add t _` unifies with `time.Second` and the like
  (noted in NetLib's header).

**Node plumbing (friction 7), in `Harness/SafeDist.lean`:**
- `NodeBootWp nd P` is "node `nd`'s boot program is safe from `P`" in the shape
  `safeDist_of_wp` needs: any local ghost state over the global one, with the node's `Assumptions`.
- `safeDist_of_boot nodes cfg Hcfg Hstart` takes:
  - the configuration premise;
  - an update from the start resources to `∃ Ps, ⌜∀ i nd, nodes[i]? = some nd → NodeBootWp nd (Ps i)⌝ ∗ [∗list] i ↦ _ ∈ nodes, Ps i`.

  It gives `SafeDist nodes cfg`, so per-node obligations come from per-index facts. It replaces the
  probe's match against a two-element `zipWith`.
- `addrs_set_proto P Q addrs` sets every address's protocols in one update:
  `([∗list] a ∈ addrs, addrTokG a ∗ addrUnsetG a) ==∗ ([∗list] a, addrTokG a) ∗ [∗list] a,
  addrProtoG a (P a) (Q a)`.
- `bigSepL_by_node` stays in `kits/paxos-m2/lean/StartExample.lean` for now. It turns a `[∗list]`
  over the addresses into one over the nodes. It may belong here.

**The probe, re-proved with these** (`Proof/dsverify_lab/harness/netprobe`). Lines exclude
comments and blanks:

| file | before | after |
|---|---|---|
| `Base.lean` | 50 | 47 |
| `Client.lean` | 199 | 153 |
| `Server.lean` | 145 | 99 |
| `Results.lean` | 150 | 136 |
| total | 544 | 435 (-20%) |

With comments and blanks the total went from 689 to 581. Where the lines went:
- `protoPrefix_echo` became `ProtoPrefixClosed.of_pure`.
- Both buffer splits became `ownSlice_take_acc`.
- Error cases need no conversion; the client's three early returns share a `ping_nil` lemma.
- `netprobe_safeDist` uses `safeDist_of_boot` and `addrs_set_proto`.

`icases` on an `Accept`/`Dial` result still needs `unfold net.newConnResult`.

## Node identity (2026-11-14)

Asked by the user for kits/epaxos-net (L1: SwiftPaxos listens on `"0.0.0.0:" + port` and `":" +
port`). A change to the trusted base.

**Semantics** (`Impl.lean`). The extension's local state is the node's IP, spelled as in the
configured addresses (`LocalState := GoString`); no step changes it, nor does a crash. `Listen(addr)`
binds `listenAddr me addr`: for a wildcard host (`wildcardHosts`: `""`, `"0.0.0.0"`, `"[::]"`, which
Go treats as the unspecified address) followed by `":" ++ port`, the node's own `me ++ ":" ++ port`;
otherwise `addr` itself. The address bound must be configured (else stuck, as before), and the
step is then the old `Listen` of that string:

```
| "Listen" => ∃ addr a : GoString, v = #addr ∧ a = listenAddr me addr ∧ a ∈ g.addrs ∧
    ((g' = g ∧ e' = Val (PairV #(W64 0) #errFail)) ∨
     ∃ lid : w64, g.listeners !! lid = none ∧
       (∀ lid' l, g.listeners !! lid' = some l → l.isOpen = true → l.addr ≠ a) ∧
       g' = { g with listeners := <[lid := ⟨a, true, []⟩]> g.listeners } ∧
       e' = Val (PairV #lid #errNone))
```

With one IP per node a wildcard listener takes exactly the connections to `"IP:port"`, and it
conflicts with a listener on `"IP:port"` both ways, as two wildcard spellings conflict with each
other (EADDRINUSE): modeling it as the listener on `"IP:port"` gives exactly that. Measured in a
private namespace with one IP (`harness/netsem/node_identity_netns_test.go`, `TestNodeIdentity`):
`Listen(":7101")`, `("0.0.0.0:7103")`, `("[::]:7105")` succeed (`Addr()` is `[::]:p` for all three),
a Dial of `10.77.0.10:p` is accepted, and `Listen("10.77.0.10:p")` and the other wildcard spellings
then fail with "address already in use"; the wildcard after the specific one fails the same way.
Other host spellings (`"localhost"`, `"[0::0]"`, a port with a leading zero) are bound as spelled,
hence stuck unless configured. A well-formed configuration has no configured address with a
wildcard host (`NetConfig.WellFormed.addrs_tame`), so a configured address is bound as spelled and
nothing changes for programs that listen on their literal addresses.

**Another node's IP.** Linux fails `Listen` on an IP the node does not have with EADDRNOTAVAIL
(measured: "cannot assign requested address", with `ip_nonlocal_bind` 0, the default and the
rig's). Decision: keep the over-approximation (success allowed, as before). It is sound for
safety, keeps the semantics independent of that sysctl, and no kit listens on another node's
address; a proof gains nothing from the failure.

**Statement** (`SafeDist.lean`). `SafeDist` has one more start premise: node `i` is on IP
`cfg.ips[i]` (`NodeIpStart ip σ`: `extLocal netConnExt σ.world = ip.spell`). This is what the rig
does (one namespace and one IP per node).

**Proof side** (`Specs.lean`). The node's local ghost state is its IP as data
(`NetConnNodeGS`, `localCtx hL me := ⌜me = hL.ip⌝`, `localStart hL me := ⌜hL.ip = me⌝`, after
Perennial's network extension); `netIp` is it and `nodeIp ip := ⌜netIp = ip⌝` the persistent
fact. The global ghost state records that no configured address has a wildcard host
(`NetConnGS.addrs_tame`, from the start's `initgP`). Specs: `wp_Listen` (unchanged statement),
`wp_Listen_at` (the general one: `Listen(addr)` binding `a`), and

```
theorem wp_ListenWild (ip h port : GoString) (hh : h ∈ wildcardHosts) :
    {{ nodeIp ip ∗ addrTok (ip ++ go!":" ++ port) }}
      (ExternalOp netConnExt.name "Listen" (Val #(h ++ go!":" ++ port))) @ s; E
    {{ (lid code : w64), RET PairV #lid #code;
       if code = errNone then listening lid (ip ++ go!":" ++ port)
       else addrTok (ip ++ go!":" ++ port) }}
```

with the Go-level `net.ListenWild.spec` / `net.ListenWild.wp_proof` (`Spec/net/Listen.lean`,
`Proof/net/Listen.lean`), `net.Listen.spec` for `ip ++ ":" ++ port` from `nodeIp ip`.
`NodeBootWpAt nd ip P` is `NodeBootWp` with `nodeIp ip.spell` given to the boot WP
(`P ⊢ nodeIp ip.spell -∗ ownGoState ∅ -∗ WP ...`), `nodeWp_of_bootAt` gets it from the extension's
local start resources and `NodeIpStart`, and `safeDist_of_bootAt` asks each node `i` for
`NodeBootWpAt nd cfg.ips[i] (Ps i)`. `safeDist_of_boot`, `NodeBootWp` and `nodeWp_of_boot` stay
(`NodeBootWp.at`). `DriverDistSpec.servers_boot` is now `NodeBootWpAt nd ip (serverRes γ i)` for
`cfg.ips[i + 1]? = some ip` (a kit-statement change; kitgen's texts updated, the kits
regenerated). `DistSpec` (`DistLemma.lean`, kit v1) is unchanged.
