# Soundness review: the TCP extension's semantics (`GooseLang/Ext/Tcp`) and `net`'s trusted models

Reviewed 2026-11-14 by the `axiom` skill, adapted to a trusted operational semantics (no `axiom`
declarations: the trust is in definitions), on branch `net-tcp` at `8ac2ca04f1`. Target: Linux
7.0.0-38-generic (this machine, default sysctls: `ip_local_port_range` 32768-60999, `mptcp.enabled`
1, `somaxconn` 4096, keepalive 7200 s), Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`; sources read in
the toolchain's `src/`).

**Verdict: refuted.** The semantics excludes a behavior Go and Linux exhibit: a `Write` of no bytes
on an end that is not closed, into a direction it has not shut, can fail, and `WriteOutcome` (D2)
lets it only succeed. `examples/axiomcx/tcp-emptywrite` panics on every run (100 of 100) and has a
closed no-panic theorem over the semantics, `emptywrite_crash_safety`, with no `sorry` and no axiom
but Lean's, the translation's axiomatized Go types and Perennial's `time.Now.wp_proof`. Everything
else attacked survives, with three findings that are not refutations of the semantics but of what
the documentation says or of what no theorem states: the zero `TCPConn`/`TCPListener` (the model is
more defined than Go, not exploitable), the address strings (D12's deployment assumption is
narrower than what it must exclude), and the closed world (no stated assumption that processes
outside the system leave the plan's addresses alone; echo's client panics against a squatter).

## What is under review

| Trusted part | File |
|---|---|
| the semantics: state, the outcome relations `ReadOutcome`/`ReadAvail`, `WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`, the steps, `timeIsZero`, the crash relation | `GooseLang/Ext/Tcp/Impl.lean` |
| the models of `net`'s functions and methods, the trusted layouts, `FieldAssumptions`, the package variables | `NetTcp/TrustedCode/net.lean`, `NetTcp/Code/net.toml` |
| the struct instances (proved from `FieldAssumptions`) | `NetTcp/ManualProof/net.lean` |
| the initial-state assumptions: `initgP g := g.conns = ∅`, `initP := True`; the start resources `tcpStart` (the plan's entries, every plan address's pending set empty), `lisStart` (the host, the initial listeners) | `GooseLang/Ext/Tcp/Ghost.lean` (`tcp_interp`), `Adequacy.lean` |
| the deployment hypotheses of the top-level theorems (`NodeStart`, the server's host `h`, `plan.lookup srvAddr = some h`, no connection) | `NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/net/*/Results.lean` |

`goose_dist_crash_adequacy` (Perennial, the framework) was read for what a theorem promises: every
thread of every node is a value or can step (`RealNotStuck`), none has an unrecovered panic. So a
behavior the model makes *stuck* only removes proofs (sound); a behavior the model *excludes* while
Go produces it is a refutation; a behavior the model *adds* is sound.

## The claims

1. D1 Read: a closed end errs; `n = 0` returns `(0, nil)` at once; else 1..n of the unread bytes,
   in order; EOF only with nothing unread and the writer done (`fin`/`cut`), and the connection may
   break at any read (a prefix kept); errors only after a cut or with a read deadline set.
2. D2 Write: closed end or own `fin`: error, nothing written. Open direction: all appended and
   success; or a proper prefix, a cut and an error; or (write deadline set) a proper prefix and a
   timeout. Cut direction: discarded, success or an error with a proper prefix count. **In every
   failure `k < len(bs)`.**
3. D3 Close: a second close errs; the first closes the end and shuts its direction; result free.
4. D4 CloseWrite: closed end errs; else shut with success, or an error changing nothing.
5. D5 SetDeadline: closed end errs; else **always succeeds**, setting the deadline iff the time is
   not Go's zero (`wall == 0 && ext == 0`); with a deadline set any operation of that kind may time
   out, and without one none does.
6. D6 Listen: stuck off the plan or another host; a failure always possible, **forced** when this
   node has an open listener at the string.
7. D7 Accept: closed listener: failure only; else a pending connection dialed to the same string,
   a failure, or waiting.
8. D8 Dial: stuck off the plan; a fresh connection (both directions open and **empty**) or a
   failure.
9. D9 LisClose: first close **succeeds**, a second fails.
10. D10/D11 crash or process exit: the node's listeners go, the network is kept.
11. Models: every failure is an `*OpError` with `Op` Go's and `Net` `"tcp"`; EOF is `io.EOF`
    itself; `Error`/`Timeout`/`Temporary` arbitrary; `Unwrap`, `Source`, `Addr`, `Err`, the other
    methods and the package variables are not modeled (stuck); a `conn`'s id is always one the
    extension returned.
12. Adequacy: the network starts with no connection; the plan is arbitrary; a node's host is kept
    by a crash.

## The refutation: an empty `Write` (claim 2)

**The gap.** `WriteOutcome st d bs k ok d'` (Impl.lean) with `st.closed = false` and
`d.status ≠ fin`: every `ok = false` clause has `k < bs.length`, so at `bs = []` the only outcome
is `k = 0, ok = true` (open direction: "all of it"; cut direction: "discarded, success"). Lean:
`emptyWrite_ok` (`NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/tcp_emptywrite/Main.lean`).

**Go and Linux.** `(*poll.FD).Write` (`internal/poll/fd_unix.go`, go1.27.3):

```go
	if err := fd.pd.prepareWrite(fd.isFile); err != nil {
		return 0, err                    // an expired write deadline: before any write(2)
	}
	...
		n, err := ignoringEINTRIO(syscall.Write, fd.Sysfd, p[nn:max])   // called for len(p) == 0 too
		...
		if nn == len(p) {
			return nn, err                // 0 == len(p): write(2)'s error returned
		}
```

and Linux's `tcp_sendmsg_locked` checks the socket's state and error (`sk_stream_wait_connect` in
`TCP_CLOSE`, `sk->sk_err`, `SEND_SHUTDOWN`) before it looks at the length, so `write(fd, p, 0)` on a
reset socket fails. Measured (`examples/net/semantics/write_test.go`, `TestEmptyWrite`, and
`examples/axiomcx/tcp-emptywrite`'s `TestEmptyWriteErrors`):

```
fresh                                  n=0 err=<nil>
expired write deadline                 n=0 err=write tcp ...: i/o timeout (timeout=true)
deadline cleared                       n=0 err=<nil>
after CloseWrite                       n=0 err=write tcp ...: write: broken pipe
empty Write after RST, no Read         n=0 err=write tcp ...: write: connection reset by peer
  and again                            n=0 err=write tcp ...: write: broken pipe
Read after RST                         n=0 err=read tcp ...: read: connection reset by peer
empty Write after RST and the Read     n=0 err=write tcp ...: write: broken pipe
```

(After `CloseWrite` the model errs too: the direction is `fin`. The deadline and reset rows are the
excluded ones.)

**The program** (`examples/axiomcx/tcp-emptywrite/emptywrite.go`; one node, plan `{127.0.0.1:7199
↦ its host}`, the deployment the semantics allows):

```go
func Main() {
	l, err := net.Listen("tcp", Addr)
	if err != nil { return }
	c, err := net.Dial("tcp", Addr)
	if err != nil { l.Close(); return }
	c.SetDeadline(time.Now())
	if _, err := c.Write(make([]byte, 0)); err != nil {
		panic("tcpemptywrite: a Write of no bytes failed")
	}
	c.Close()
	l.Close()
}
```

Go (`TestMainPanics`, each run in its own process, `repeat.sh`-style loop): **100 of 100 runs
panic** (`tcpemptywrite: a Write of no bytes failed`). A variant without a deadline
(`mainReset`, in the test file: the acceptor closes with a byte unread, so Linux sends a RST; the
dialer's `Read` takes `ECONNRESET`; the empty `Write` returns `EPIPE`): **50 of 50 runs panic**.

**The proof.** Translated by the pinned goose (project `nettcp`, package
`../axiomcx/tcp-emptywrite`; `NetTcp/{Code,GeneratedProof}/github_com/mit_pdos/etcd_grove/examples/axiomcx/tcp_emptywrite.lean`;
package init by `etc/gen-init.py`, `NT_PKGS`/`NT_PROGRAMS`). `Main.lean`'s `wp_Main` is the triple
`{{ isPkgInit pkg ∗ tcpPlan G addr host ∗ inv addrN (addrInv addr (fun _ => True)) }} Main #()
{{ RET #(); True }}` from the Go-level specs of `net` (`Listen`, `Dial`, `Conn.SetDeadline`,
`Conn.Write`, `Conn.Close`, `Listener.Close`, all proved from the trusted models over the
extension) and `time.Now.spec`; the `Write`'s outcome is `emptyWrite_ok` (the end not closed after
`SetDeadline`: `DeadlineOutcome` of a fresh end). `Results.lean`'s `emptywrite_crash_safety` is the
closed theorem over `goose_dist_crash_adequacy` (as `shutdown_crash_safety`): in every execution with
crashes of the node, from a local state with no package initialized and its main thread, the plan
having `Addr` at the node's host and the network no connection, no thread is stuck and none has an
unrecovered panic. `lake build ...tcp_emptywrite.Results`: built; `#print axioms
emptywrite_crash_safety`: `propext`, `Classical.choice`, `Quot.sound`, the translation's
axiomatized Go types (`net.Dialer`, `net.netFD`, ..., `sync.Map`, ...: the list `echo_crash_safety`
prints, counted as Perennial's) and `time.Now.wp_proof` (Perennial's, which `preface_crash_safety`
also prints; the refutation does not use what it says: the empty `Write` succeeds in the model
whatever the deadline, and the deadline-free `mainReset` shows the same gap).

**What rests on it.** No example proof writes an empty buffer where its check depends on the
result (framed's server may write an empty payload, and breaks on an error), so no exported result
is known to be false; but every theorem over the extension is a theorem about a semantics with this
gap.

**Proposed restatement (not applied: a trusted change, for the user).** In `WriteOutcome`'s three
failure clauses, replace `k < bs.length` by `k < bs.length ∨ k = 0` ("a failure writes a proper
prefix, or nothing": for `bs ≠ []` the same, for `bs = []` it adds the failures), and in D2's prose,
after "Go's Write returns fewer bytes than asked only with an error": "and an empty Write may fail
(an expired deadline, a reset)". The extension's specs state `WriteOutcome` verbatim, so only proofs
that use its success at `bs = []` change. `TestEmptyWrite` is the decision's test.

## Findings that are not refutations

### F1. The zero `TCPConn` and `TCPListener` (models more defined than Go)

`TrustedCode/net.lean` says "Go code outside `net` cannot make a `conn` (its type is unexported),
so `id` is always an id the extension returned". False: `var c net.TCPConn` (and `&net.TCPConn{}`,
`var l net.TCPListener`) is legal outside `net`; its `fd` is nil and every method returns the bare
`syscall.EINVAL` (not an `*OpError`) touching nothing (`!c.ok()`, `net.go`, `tcpsock.go`; measured,
`errors_test.go`, `TestZeroValues`). In the models its id is 0, which is `endId 0 false` (connection
0's dialer end) or listener 0 once `DialStep`/`ListenStep` choose that number (both allow it): an
operation on the zero value then acts on that connection or listener (a `Write` appends to
connection 0, a `Close` closes it), where Go does nothing. Not exploitable: the extension chooses
connection and listener numbers freely, a proof cannot make it choose 0, and on any other choice
the zero value's operation is stuck; Go's own behavior on it (an `EINVAL` with no effect) is never
the model's for an open direction. But a model may be less defined than Go, never more. **Fix:**
make 0 name nothing (`DialStep` with `0 < c`, `ListenStep` with `l ≠ 0`, or ids offset by one), and
correct the docstring; then the zero value is stuck, as the docstring intends.

### F2. Address strings (D12's deployment assumption is too narrow)

D7 accepts at a listener only the connections dialed to the same string, and D12 assumes "the
plan's strings must name distinct sockets (no two strings for one `host:port`)". Measured
(`addr_test.go`, `TestAddressAliases`): a listener at `127.0.0.1:P` accepts Dials of `localhost:P`
and `:P`; a wildcard listener at `:P` accepts Dials of `127.0.0.1:P` and `127.0.0.2:P`; with `:P`
open, `Listen("127.0.0.1:P")` fails (`EADDRINUSE`). A plan `{":P", "127.0.0.1:P"}` names two
different `host:port` pairs, so D12's wording does not exclude it, yet a Dial of `127.0.0.1:P`
reaches the listener at `:P`, which the model excludes (a server at `:P` that writes to what it
accepts, a client at `127.0.0.1:P` whose proof holds that address's pending set and knows nobody
accepts there, so it never reads a byte: provable, and false). Likewise a hostname whose resolution
changes between calls (a second `Listen` of the same string succeeding on another address, which
D6 forbids), and port 0 (D12 lists it, but no theorem's hypothesis does). **Fix:** state the
assumption as what the model needs: "a `connect(2)` to the address a Dial of plan string `a`
resolves to reaches only sockets bound by `Listen(a)` at `a`'s host, and every Listen or Dial of
`a` resolves to the same address (no wildcard overlapping a specific address, no two names of one
address, no port 0)", and put it (with F3 and F4) in one place that every `Results.lean` names.

### F3. The closed world (no theorem states it)

The model's network holds only the system's nodes: only a node at the plan's host can Listen at a
plan address (D6), and every connection is dialed by a node. Real processes outside the system can
listen at or dial a plan address. `examples/axiomcx/tcp-squat` (a test only): a process that is not
one of echo's nodes listens at echo's `SrvAddr` before the server (whose `Listen` then fails, which
D6 allows) and replies `"jello"`; echo's client, run as echo runs it, connects to it and **panics**
(`echo: the reply is not the request`), while `echo_crash_safety` says it never does. Likewise an
outside dialer sending bytes to a server whose proof assumes only the system's clients connect
(echo models one junk sender as a node; an arbitrary number of outside dialers is not covered by
any theorem). This is a deployment assumption, but it is stated nowhere (the header says the plan
names "the host that may listen at it", not that nothing else does). **Fix:** state it with F2:
"every process that listens at or dials a plan address is a node of the system".

### F4. The target configuration is not named

The file extension claims one configuration (`notes/axiom-review/fs-config/`); the TCP extension
says "Linux" and its tests ran on this machine's defaults. Two claims depend on them: Go 1.27's
listeners are MPTCP by default (`defaultMPTCPEnabledListen = true`, `dial.go`; `mptcp.enabled` 1
here), so the measured accepted ends are MPTCP fallback sockets; and D8's "both directions empty"
needs a Dial not to connect to itself (TCP simultaneous open), which needs the plan's ports outside
`ip_local_port_range` (32768-60999 here; Go's `selfConnect` guard, `tcpsock_posix.go`, retries only
twice and then returns the self-connected conn). **Fix:** name the configuration (Linux 7.0, default
sysctls, plan ports outside the ephemeral range, default `GODEBUG`) in the header and `doc.go`.

## Attacks that failed (claim by claim)

| # | Attack | Outcome | Evidence |
|---|---|---|---|
| 1 | Read: an error on an open, deadline-free direction that the model has not cut (RST, ETIMEDOUT, EHOSTUNREACH after retransmissions) | allowed: a read may cut its direction at any time | D1's last clause; `reset_test.go`, `process_test.go` |
| 2 | Read: EOF while the writer never closed (killed process's kernel FIN; a RST whose error a Write took) | allowed (the 2026-11-14 fix) | `TestKilledWriterFin`, `TestResetErrorTakenByWrite` |
| 3 | Read: `n = 0` forced `(0, nil)`: with an expired deadline, a pending RST, bytes | Go returns `(0, nil)` before `prepareRead` | `fd_unix.go` `Read`; `TestReadEmptyBuffer` |
| 4 | Read: bytes and an error together; more than `len(b)` | never: `n = 0` on error; `maxRW` only truncates | `fd_unix.go` |
| 5 | Read: data after a RST lost or kept | either: the cut keeps any prefix | `TestResetCloseUnreadInput` (kept) |
| 6 | Write `len > 0`: `(len, err)` | never: `nn == len(p)` only after a write(2) that succeeded | `fd_unix.go` `Write` |
| 7 | Write blocked, then the own end's Close or CloseWrite (not serialized with the Write: `Shutdown` takes only a reference): `(nn, err)` with `nn > 0` and the peer reading exactly `nn` bytes then a clean EOF | allowed: the Write's step chooses "prefix `nn`, cut" before the Close; a cut direction reads as EOF | the model's nondeterminism; CloseOutcome on `cut` |
| 8 | Write: peer reads bytes of a Write that later fails | allowed: the Write's step (prefix, cut) linearizes before the reads | as 7 |
| 9 | Write of a deadline-free open direction failing with no reset (ENOBUFS/ENOMEM) | not modeled, as D12 says (memory exhaustion) | D12 |
| 10 | Write after the peer's FIN, after a RST | success (lost) or EPIPE: both allowed | `TestWriteAfterPeerClose`, `TestWriteToKilledPeer` |
| 11 | **Write of no bytes** with an expired deadline, after a RST | **refuted** | above |
| 12 | Close twice; Close of a reset end | `ErrClosed`; nil: allowed | `TestCloseTwice`, `TestCloseAfterReset` |
| 13 | Close concurrent with a blocked Read / Accept | the blocked call fails: allowed (it waits, then sees the closed end/listener) | `TestCloseUnblocksRead`, `TestAcceptAfterListenerClose`; shutdown's proof |
| 14 | Close with unread input: RST instead of FIN | the peer's cut covers ECONNRESET and the lost bytes | `TestResetCloseUnreadInput`, `TestResetLingerZero` |
| 15 | CloseWrite twice; after both FINs; after a reset (ENOTCONN, the direction unchanged in the model, while Linux's later writes fail) | nil, ENOTCONN, ENOTCONN: allowed; the later non-empty writes may fail in the model; the empty one is 11 | `TestCloseWrite`, `TestCloseWriteAfterReset` |
| 16 | SetDeadline forced success on an open end: a non-pollable socket (`ErrNoDeadline`)? | never for a TCPConn: a poller failure fails the Dial or Accept that makes the socket (`netFD.init`) | `fd_unix.go`/`fd_poll_runtime.go`, `sock_posix.go` |
| 17 | `timeIsZero` vs `Time.IsZero` | identical (`t.wall == 0 && t.ext == 0`, `time.go:262`); Perennial's `time.Time` is the translated struct (`wall`, `ext`, `loc`); a non-zero time always sets a deadline (`setDeadlineImpl`: `d == 0` becomes `-1`) | go1.27.3 `time.go`, `fd_poll_runtime.go` |
| 18 | A timeout without a deadline (keepalive, `TCP_USER_TIMEOUT`) | those are ETIMEDOUT, a broken connection: a cut | — |
| 19 | Listen forced failure at an own open listener; across a crash; across `os/exec`'s fork window | EADDRINUSE; success after a crash is allowed but not forced; the fork window only adds failures | `TestListenTwice`, `child_test.go` |
| 20 | Accept on a closed listener; pending connections at a listener's Close or a crash | failure only; Linux resets them, which the dialer sees as a cut | `TestAcceptAfterListenerClose`, `TestPendingAtListenerClose`, `TestKilledListener` |
| 21 | Dial returning a connection with bytes already readable (self-connect, another listener) | needs a plan port in the ephemeral range (F4) or an outside process (F3) | `tcpsock_posix.go` `selfConnect` |
| 22 | Error values: a bare error where the model has an `*OpError`; `Op`/`Net` | every failure on values Listen/Dial/Accept returned is an `*OpError`, `Net` `"tcp"`, the model's `Op` (Close and CloseWrite `"close"`, deadlines `"set"`); EOF is `io.EOF` | `errors_test.go`, `TestErrorsAreOpErrors`; `net.go`, `tcpsock.go`, `dial.go` |
| 23 | `errors.Is(err, net.ErrClosed)`, `errors.Is(err, os.ErrDeadlineExceeded)`, `err.(interface{ Unwrap() error })` | the assertion succeeds in both (`*OpError`'s method set is Go's, `Unwrap` included); calling `Unwrap` has no `MethodUnfold` (no proof); `net.ErrClosed` is not allocated (loading it is stuck); Perennial's `errors.Is.spec` needs an `errorWalkTree` whose unwrap relation must come from the type's `Unwrap` | `NetTcp/Code/net.lean` `OpError.TypeAssumptions`; `Perennial/Spec/errors/Is.lean` |
| 24 | `Error()`, `Timeout()`, `Temporary()` | arbitrary in the model: a superset | — |
| 25 | Zero `TCPConn`/`TCPListener` | F1 (not exploitable) | `TestZeroValues` |
| 26 | Struct copies and comparisons of `TCPConn` (`*tc` copied, `==`) | ids compare as Go's `fd` pointers do, except the zero value (model: equal to connection 0's dialer end; Go: never): extra model behaviors only | — |
| 27 | Field accesses, allocation in the models (`FieldAssumptions`, the struct instances) | the standard struct-field steps on the trusted layouts; the instances are proved | `ManualProof/net.lean` |
| 28 | A network other than `"tcp"`, a nil receiver | the model panics or is stuck: less defined than Go | `Dial.impl`, `Listen.impl` |
| 29 | Process exit (`main` returns): the other goroutines die, the kernel closes the sockets | the model keeps the goroutines running (more behaviors); the peers' view is a cut | D11 |
| 30 | Machine crash: buffered bytes lost on the dead machine, nothing sent until the peer's timeout or a reboot's RST | the peer's reads may wait, cut with a prefix; its writes succeed or fail | D1, D2, D10 |
| 31 | The initial state: `initgP` (no connection), `initP` True, an arbitrary initial `lis` | true of a starting system; an arbitrary `lis` only strengthens the theorems | `Ghost.lean` |
| 32 | The closed world (outside listeners and dialers) | F3: an unstated assumption; echo's client panics against a squatter | `examples/axiomcx/tcp-squat` |
| 33 | Address aliases | F2 | `TestAddressAliases` |

Not tried: undetected corruption (TCP's checksum; an accepted assumption, which D12 could list),
memory exhaustion (D12), IPv6-only hosts, `GODEBUG` variations (`multipathtcp=0`), Dials that time
out against an unreachable host (a failure, allowed).

## Recommended changes (none applied: the semantics and the models are trusted)

1. `WriteOutcome` (D2): a failure writes `k < bs.length ∨ k = 0` bytes (above), and D2's prose.
2. Ids: make 0 name no connection end and no listener (F1), and correct the model's docstring.
3. A "Deployment" paragraph in `Impl.lean`'s header, named by every `Results.lean`: the closed
   world (F3), the address strings (F2), no port 0, and the configuration (F4).
4. `notes/net-tcp.md` still describes the first semantics (`tcpOut`, broken ends, "no process
   exit"): bring it to v2.
5. `doc.go` lists `TestEmptyWrite` as REFUTES D2: once 1 is applied, change it to "allowed".

## Applied (2026-11-14, the same day; semantics v2.1)

All four recommendations were applied in `GooseLang/Ext/Tcp/Impl.lean`:

1. **The refutation**: `WriteOutcome`'s three failure clauses now allow a prefix shorter than asked
   *or nothing* (`k < bs.length ∨ k = 0`), D2's prose says why (`TestEmptyWrite`, now "allowed").
   `emptywrite_crash_safety` no longer holds: the counterexample's translation and proof were taken
   out of project `nettcp` (`etc/goose.py`, `etc/gen-init.py`); the program and its test remain in
   `examples/axiomcx/tcp-emptywrite` (it still panics, as it should).
2. **F1**: `DialStep` numbers no connection 0 and `ListenStep` gives no listener id 0, so id 0 (a
   zero-value `TCPConn`/`TCPListener`) names nothing and its operations are stuck (less defined than
   Go's `EINVAL`: sound); the trusted models' docstring says so.
3. **F2–F4**: a "Deployment" paragraph (D13) in `Impl.lean`'s header: a closed world, addresses that
   do not alias (canonical `IP:port`, no hostnames or wildcards, no two strings the kernel confuses),
   ports outside the ephemeral range, and the target configuration (Linux 7.0 defaults, Go 1.27.3).
4. `notes/net-tcp.md` rewritten for the current semantics.

The seven examples' proofs were re-checked over the revised semantics.

