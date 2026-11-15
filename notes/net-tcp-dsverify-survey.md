# dsverify-lab's network model against ours: the survey (2026-11-14)

A read-only survey (a subagent's report, kept as written but for headers) of dsverify-lab's `NetConn`
model at its `origin/master` `91cebb8` ("B": `/home/ubuntu/dsverify-lab`, read with `git show
origin/master:<path>`) against our v2.1 ("A"). The decisions taken from it are in
`notes/net-tcp-v3-plan.md`. Line numbers are at those commits.

## Changed in B since the earlier comparison (5cae9a7)

- `LocalAddr`/`RemoteAddr`: non-nil `*TCPAddr` with an arbitrary `String()` (28da823); `Listener.Addr`
  new (0914f5c); `DialTimeout` with "abandoned" connections (F1); a node's IP is its extension local
  state (13399a8); **an `errBroken`/`errClosed` Write now appends exactly its first `k` bytes**
  (41a7f83: B converged to A on F3). Unchanged: `ErrClosed`, `Timeout()` true for deadline timeouts,
  `NetConfig.WellFormed`, a break cuts both streams, no crashes.

## 1. Error identities and the Write/Close race (F2) — ADOPT-MODIFIED

- **B.** Every failure is a translated `&OpError{Op, Net, Source, Addr, Err}`; `OpError`,
  `OpError.Unwrap` translated (`Harness/Code/net.toml:7-12`). `Err` from `model.codeErr`
  (`TrustedCode/net.lean:206-211`): a timeout `&connError{true,true}`; a closed end the model-only
  pointer `net#model.errNetClosing`, which `ErrClosed.init` (`net.lean:450-456`) also stores in
  `net.ErrClosed`; anything else `connError` with arbitrary `Timeout()`/`Temporary()`. Result codes
  `errNone, errEOF, errTimeout, errClosed, errBroken, errFail` (`Impl.lean:185-197`). F2:
  `WriteOutcome` lets a Write at an open end return `errClosed` with its first `k` bytes appended
  (`Impl.lean:231-235,253`).
- **A.** `OpError` trusted `{Op, Net}` (`NetTcp/TrustedCode/net.lean:133-146`); `Error`, `Timeout`,
  `Temporary` arbitrary (`:325-335`); `ErrClosed.init` does nothing (`:415`); no `Unwrap`/`Err`, so
  `errors.Is` is stuck. Results coarse: `ReadRes.err`, `ok : Bool` elsewhere. F2 admitted only through
  the cut outcome, sound only because the error's identity is unobservable.
- **Evidence (B).** Measured: `netsem/err_closed.go:12-34` (Is-ErrClosed true for the own-closed-end
  cases, including a blocked Read or Accept closed by another goroutine; false for EOF, timeout,
  ECONNRESET, EADDRINUSE, ECONNREFUSED); `write_close_race.go:19` ((k>0, ErrClosed), the peer reads
  exactly k); on veth `veth_test.go:284` `timeoutOnBreak` (ETIMEDOUT has `Timeout()` true and is not
  `os.ErrDeadlineExceeded`). Go 1.27.3: `net.go:743,750` (`ErrClosed = poll.ErrNetClosing`),
  `fd_unix.go` `FD.Write` (a blocked `waitWrite` returns `nn, ErrNetClosing`), `fd_posix.go:70`
  (Errnos wrapped as `*os.SyscallError`).
- **Why modified.** Not B's model-only `connError` (unsound, S1 below): Perennial translates
  `poll.ErrNetClosing`, `poll.ErrDeadlineExceeded` (`Perennial/Code/internal/poll.toml`) and sets
  `os.ErrDeadlineExceeded` from it (`Code/os.lean:916-929`), so A can return Go's real values. Three
  constraints: identities **require** F2; `Timeout()` must stay arbitrary for breaks (ETIMEDOUT);
  the break error must have Go's dynamic type (`*os.SyscallError`).
- **Sketch.** `TcpErr = closed | timeout | broken`; `ReadRes.err e`, `ok : Bool` → `Option TcpErr`;
  F2 disjunct `(k < bs.length ∨ k = 0) ∧ res = some .closed ∧ d' = {d with bytes := d.bytes ++ bs.take
  k}` on an open direction; Accept on a closed listener `.closed`. Translate `OpError` (5 fields),
  `OpError.Unwrap`, `errClosed`/`ErrClosed`; `Err` := `poll.ErrNetClosing` / `poll.ErrDeadlineExceeded`
  / `&os.SyscallError{Syscall: AnyString, Err: syscall.Errno(any nonzero)}`. Tests: B's ErrClosed
  matrix; `errors.Is(err, os.ErrDeadlineExceeded)` with `Timeout()` true for read and write deadlines;
  `Err` a `*os.SyscallError` wrapping an Errno for ECONNRESET, EPIPE, ECONNREFUSED, EADDRINUSE,
  ENOTCONN; `TestWriteCloseRace` (1 MiB Write to a slow reader, Close from another goroutine: k>0,
  ErrClosed, the peer reads exactly k).

## 2. The conformance checker (`harness/conform`) — ADOPT-MODIFIED

- **How B's works** (`notes/conform.md`, `harness/conform/README.md`).
  - Tracer: `overlay.py` writes a `go build -overlay` file renaming 31 traced `func` lines in Go's own
    `net.go`, `dial.go`, `tcpsock.go`, `tcpsock_unix.go` to `conformOrig<Name>` (plus `newTCPConn`'s
    `SetKeepAliveConfig` call), failing unless each rename matches one line;
    `trace/zz_conform_trace.go.src` (709 lines) defines wrappers with the public names, each writing a
    `B` record, timing with `runtime.nanotime`, calling the original, writing an `E` record; one JSON
    line per `write(2)` (SIGKILL loses no returned call). Records: op, socket id (`c<k>`/`l<k>` by
    `*netFD`, never reused), arguments (buffer length, written bytes in hex, deadline kind and
    set/cleared, address, API), results (count, bytes read, new socket with local/remote addresses),
    the error's raw facts (EOF, Is ErrClosed/ErrDeadlineExceeded, Op/Net, Timeout/Temporary, errno,
    Error()); header pid, node id, addresses, time and network namespaces, a wall/monotonic pair.
    Without the overlay the binaries are byte-identical.
  - Clock checks: one time namespace; an Accept returns after its Dial is called; every end operation
    returns after the call that made the end.
  - Mapping and rules: errors to result codes (as `connResult`/`codeErr`); shape rules (EOF unwrapped
    and only from Read; every other error an `*OpError` with Go's `Op`; closed means
    Timeout/Temporary false/false; deadline true/true; addresses non-nil and fixed); scope rules for
    what the model has no step for (other networks, unmodeled APIs, unconfigured addresses, port 0).
  - Decomposition: one component per bound address (listeners, Accepts, successful Dials), one per
    connection (both ends). Pairing by swapped 4-tuples; a reused 4-tuple takes the latest causal
    Dial; else up to 100 injective pairings; an unpaired Accept explained by a Dial that never
    returned or a failed Dial from the same host.
  - Search: `lincheck.py` (149 lines), Wing & Gong with Lowe's memo over (linearized set, state),
    strict real-time order. Lazy breaks (break only when an op fails otherwise; completeness by a
    simulation `S ≥ S'`, `notes/conform.md:54-89`); lazy prefixes (a cut stream stands for every
    prefix); ops that never returned left out except Writes, which may linearize with all bytes.
  - Model: `model.py` (276 lines), a hand transcription of the outcome relations and step cases with a
    table to their Lean names (README:223-249); not proved.
  - Tests: `test_conform.py` 62 tests (positive hand-made and real traces, negative traces asserting
    the failing op, model units); `mutate.py` six mutant kinds, all 528 rejected. Probe (`probe/`):
    `dialrace`, `closewrite`, `resetwrite`.
  - Findings (`notes/conform.md:207-270`): F1 a failed `DialTimeout` left a connection that `Accept`
    returned, reading EOF; F2 a Write returned (k>0, ErrClosed) and the peer read its bytes; F3 a
    Write returned (k>0, ECONNRESET) and the peer read its bytes. All three excluded by B's model then;
    fixed (41a7f83). All 108 kit runs admitted.
- **A has** per-decision tests and process tests checking only "no panic"; nothing checks whole runs
  against `TcpStep`.
- **For A.** The tracer almost verbatim (same Go, same four files; trace `CloseWrite`; node from an
  environment variable, pid recorded so a restart is a crash event; `proctest.Build` adds
  `-overlay`). A mirror of `Impl.lean`'s relations and steps, components per connection (two
  directions and two ends), per plan address (the pending set), per node (its listeners, a crash
  between one process's last record and the next's first). Lazy cuts per direction (one corner: after
  a cut, `CloseWriteOutcome` keeps `cut`, so a later Write may succeed, while from `fin` it cannot;
  Go never produces that trace, but write it into the completeness argument). Reuse `lincheck.py`.
  Certify ADMITTED: Bool versions of the outcome relations with `↔` lemmas in Lean; the search outputs
  its witness (the linearization, each read's `k`, each cut's kept length); a `lake exe` replays it
  through the proved deciders. Inputs: the examples' process tests, the semantics tests traced, a
  probe (Write/Close and Write/CloseWrite races, a reset during a 1 MiB Write, a kill mid-Write,
  partial writes past a deadline, empty Writes, a Dial with no listener then Listen); B's mutants as
  tests. Run on an etcd cluster it would list the `net` APIs etcd, grpc and net/http call. Size:
  tracer ~750 Go lines, checker and model ~900 Python, replay 300–500 Lean.

## 3. Address well-formedness as a decidable premise — ADOPT-MODIFIED

- **B.** `NetConfig.WellFormed` (`SafeDist.lean:113-125`, decidable): one unicast IP per node
  (`IPv4.Unicast` 74-75: not 0/8, 127/8 or ≥224), every endpoint on one of them, port 1..65535,
  canonical `Endpoint.spell` (100-101), no duplicates; a conjunct of `SafeDist` (236-246), proved by
  `decide` (153-156); `addrs_tame` (138-150).
- **A.** D13 is prose (`Impl.lean:84-94`); theorems assume only `plan.lookup srvAddr = some h`.
- **For A.** `PlanWellFormed plan := ∀ a ∈ plan.keys, ∃ e, a = e.spell ∧ e.ip ∉ {0.0.0.0/8,
  multicast/broadcast} ∧ e.port ∈ [1,32767] ∪ [61000,65535]` (loopback allowed: A's deployment is one
  machine; the port clause is D13's ephemeral-range condition: Go's `selfConnect` guard retries only
  twice, `tcpsock_posix.go:111`); a premise of every `Results.lean` theorem, an `example … := by
  decide` per plan.

## 4. `LocalAddr`, `RemoteAddr`, `Listener.Addr` — ADOPT

- **B.** `netFD` holds `laddr`/`raddr` (`net.lean:89-94,143-148`); `Dial`/`Accept` store two fresh
  arbitrary non-nil `*TCPAddr`s (`arbitraryAddr` 179-188; `Dial.impl` 313-314; `Accept.impl` 336-337),
  `Listen` one (296); the getters return the stored value (353-356, 390-395); `TCPAddr.String`
  arbitrary (436); `TCPAddr`, `IP` translated (`net.toml:12`).
- **Evidence.** Documented: `sock_posix.go`'s `fd.dial` takes the remote from connect, else
  getpeername, else the dialed `*TCPAddr` (never nil); local from getsockname (Linux's `inet_getname`
  does not fail for an open socket). Measured: a wildcard listener's `Addr` is `[::]:p`. Caution: Go's
  `tcpsock_posix.go:130-136` says "the socket constructor can return an fd with raddr nil under
  certain unknown conditions"; on Linux IPv4 the paths above rule it out: say so.
- **Why.** net/http's `conn.serve` calls `RemoteAddr().String()`, grpc's `Serve` calls `lis.Addr()`.
- **For A.** `conn {id; laddr Addr; raddr Addr}`, `TCPListener {lid; addr Addr}`; translate `TCPAddr`,
  `TCPAddr.Network`, `IP`; `TCPAddr.String` `AnyString`; an `"AnyW64"` op for the port; measured: the
  values are non-nil `*TCPAddr`, equal across calls, unchanged after Close and after a reset.

## 5. `DialTimeout` and abandoned connections (F1) — ADOPT-MODIFIED

- **B.** The third `Dial` case: a failure leaving `Conn.abandoned` pending, the dialer's end closed and
  its stream `fin` and empty (`Impl.lean:141-142,329-332`); `DialTimeout.impl` is `Dial.impl`.
- **Evidence.** Measured `dial_timeout_accepted.go:10-28`: of 5000 DialTimeouts of 1–60 µs, 1922
  failed and 1811 of those were accepted, each reading EOF.
- **Why.** Plain `Dial` in A's configuration is sound today; with `DialTimeout`/`DialContext` (grpc,
  net/http) F1 is mandatory, and for any claim covering network-injected resets.
- **For A.** `TcpConn.abandoned a`; `DialStep` gains the abandoned failure for every Dial;
  `DialTimeout.impl` is `Dial.impl` with the timeout error; the address protocols are prefix-closed, so
  an empty stream satisfies them, but every example's proof handles it; port the test.

## 6. Wildcard `Listen` — ADOPT-MODIFIED

- **B.** A node's IP as its extension local state (`Impl.lean:280-284,386-388`); `listenAddr me addr`
  resolves `""`, `"0.0.0.0"`, `"[::]"` to `me:port` (`Impl.lean:164-178,309`); one netns per node.
- **Evidence.** `node_identity_netns_test.go:12-23`: all three spellings succeed, `Addr` is `[::]:p`,
  reached by `Dial(IP:p)`, conflicting with `IP:p` both ways; A's `TestAddressAliases` measures ":P"
  taking 127.0.0.1:P and 127.0.0.2:P.
- **For A, without netns.** `Listen(h:p)` with a wildcard `h` resolves to the unique plan address with
  port `p` and host `L.host`; stuck if none or if the port is not unique in the plan.

## 7. Tests in network namespaces — ADOPT

- **B.** `veth_test.go:112-366` over `run-veth.sh` (namespaces on a bridge, netem); `timeoutOnBreak`
  (284): an iptables partition with `TCP_USER_TIMEOUT` 2 s, keepalive, or `tcp_retries2=3` gives
  ETIMEDOUT with `Timeout()` true, then EOF and EPIPE; `acceptOrder` (141); `break_netns_test.go:18`
  (an iptables-made reset).
- **A.** "Not measured: a machine crash, unreachable addresses and Dial timeouts" (`doc.go`); the
  review's ETIMEDOUT-is-a-cut row has no evidence. Here unprivileged user namespaces are blocked, but
  `sudo -n` works (B's `sudo -n unshare -n test.binary` pattern).

## 8. Lean tests of the semantics — ADOPT

B's `Ext/NetConn/Tests.lean`: `example`s, outside the trust base, that each decision allows or
excludes the outcome its docstring says. For A: `GooseLang/Ext/Tcp/Tests.lean`, one per `doc.go`
row, naming its Go test; a "Lean" column in `doc.go`.

## 9. Documented and assumed evidence classes — ADOPT (minor)

B's `documented.go:12-96` (AcceptAnyOrder, ReadShape documented with citations; AddressSpelling,
InOrderOnce assumed). For A: assumed rows for in-order once / no corruption and the closed world;
documented rows for code citations.

## 10. Close of an open end never fails — ADOPT-MODIFIED (low value)

B: `errNone` on an open end (`Impl.lean:260-266`). A: unconstrained. Evidence: `poll.FD.Close` (the
fd destroyed on the last reference; TCP's close returns 0), A's `TestCloseTwice`/`TestCloseAfterReset`
measure nil.

## Skipped

`"tcp4"`; a break that cuts both streams (A's per-direction cut allows more); pending connections owned
by the listener (impossible under A's node-local crashes, D7); `Listen` on another node's address
succeeding; B's Hoare-triple token specs; the model-only error type (S1); `t == time.Time{}`.

## Soundness problems found

- **B, S1 (likely unsound).** `Err` values of a model-only type `*net#model.connError`, while Go
  returns `*os.SyscallError` (`fd_posix.go:70`); `OpError.Err` is a translated readable field, so a
  type assertion toward `*os.SyscallError` decides false in the model, true in Go. Program: dial a
  configured address with no listener, `if _, ok := err.(*net.OpError).Err.(*os.SyscallError); ok {
  panic("x") }` (Go panics every run; ECONNREFUSED). Not proved.
- **B, S2 (minor).** `WellFormed` allows ephemeral ports; a Dial to one's own address with no
  listener can self-connect, which B excludes.
- **A, traps if B's ideas are adopted naively.** A1: identities without F2 are unsound. A2:
  `Timeout()` "true iff deadline" is unsound (ETIMEDOUT). A3: `DialTimeout`/`DialContext` without F1
  is unsound. A4 (precision): a Write may succeed after the end's own `CloseWrite` if the direction was
  cut earlier (`CloseWriteOutcome` keeps `cut`); Go returns EPIPE. A5: D13 in no theorem's hypotheses.
