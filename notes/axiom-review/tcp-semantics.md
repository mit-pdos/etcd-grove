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

## v3 (2026-11-14)

Reviewed by the `axiom` skill, adapted to a trusted operational semantics, on branch `net-tcp` at
`da41275c2a`: semantics v3 (commits `c974721af7`, `0be9b1f622`, `580758abba`;
`notes/net-tcp-v3-plan.md`, D14-D21), the same target (Linux 7.0.0-38-generic, default sysctls,
Go 1.27.3, sources read in `/usr/local/go/src`). Read whole: `GooseLang/Ext/Tcp/{Impl,Deploy,Ghost,
Adequacy}.lean`, `NetTcp/TrustedCode/net.lean`, `NetTcp/Code/net.toml`, `net`'s package fact and
initializer (`NetTcp/Proof/net/{Base,Init}.lean`) and the copied initializers of `os`,
`internal/poll`, `syscall` (proved from their translations, so they add no trust).

**Verdict: refuted.** A `Write` is one step of the semantics, and `WriteOutcome` (D2) lets it time
out only if the end's write deadline is set *at that step*. Go's `Write` is a loop of `write(2)`
calls that checks the deadline in every wait: a deadline set by another goroutine while the `Write`
blocks, after the peer has read some of its bytes, makes it return `(n, os.ErrDeadlineExceeded)`.
In the semantics the bytes the peer read must have been appended by the `Write`'s step, which
therefore came before the deadline was set: the timeout is excluded.
`examples/axiomcx/tcp-writedeadline` panics in 99 of 100 runs and has a closed no-panic theorem
over the semantics, `writedeadline_safety`, with no `sorry` and no axiom but Lean's, the
translation's axiomatized Go types and Perennial's `time.Now.wp_proof` (the list
`emptywrite_crash_safety` printed). Everything else attacked survives (the table below).

### R1. A deadline set while a `Write` blocks (D2, D5)

**The gap.** `WriteOutcome st d bs k res d'` (`Impl.lean`): every clause with `res = some .timeout`
has `st.wdl = true`, `st` the end's state at the `Write`'s one step; on an open direction the same
step appends the `k` bytes it counts. Lean: `write_noTimeout`
(`NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/tcp_writedeadline/Main.lean`).

**Go and Linux.** `(*poll.FD).Write` (`internal/poll/fd_unix.go`, go1.27.3): `prepareWrite` checks
the deadline once, then the loop calls `write(2)` and, on `EAGAIN`, `fd.pd.waitWrite`, which returns
`ErrDeadlineExceeded` as soon as the write deadline passes, including a deadline set after the
`Write` began (`SetDeadline`/`SetWriteDeadline` re-arm the poller's timer,
`runtime_pollSetDeadline`, and wake a waiter whose deadline has passed); the `Write` returns
`(nn, err)`, `nn` the bytes already in the kernel. Measured (`examples/axiomcx/tcp-writedeadline`,
`TestWriteDeadlineSetDuring`, `-count=20` passes): a 32 MiB `Write` on a loopback connection
blocks; the peer reads one byte; another goroutine sets the writer's deadline
(`SetDeadline(time.Now())`, or `SetWriteDeadline(time.Now().Add(100ms))`, which expires while the
`Write` blocks):

```
now:    Write = (2633835, ...: i/o timeout), Err *poll.DeadlineExceededError, Timeout true; the peer read 2633835 bytes, then EOF
future: Write = (2633835, ...: i/o timeout), Err *poll.DeadlineExceededError, Timeout true; the peer read 2633835 bytes, then EOF
```

The `Err` is `os.ErrDeadlineExceeded` itself, `0 < n < len`, and the peer reads exactly `n` bytes:
the shape of `TestWriteDeadlinePrefix`, whose deadline is set *before* the `Write` (the case the
semantics covers). `TestWriteCloseRace` is the same race with `Close`, which D15 covers because its
`closed` clause has no precondition on the end's state.

**The program** (`examples/axiomcx/tcp-writedeadline/writedeadline.go`; one node, plan
`{127.0.0.1:7197 ↦ its host}`, well formed):

```go
func reader(a, c net.Conn) {
	b := make([]byte, 1)
	if _, err := a.Read(b); err == nil {
		c.SetDeadline(time.Now()) // one of the Write's bytes arrived: the Write has started
	}
}

func Main() {
	l, err := net.Listen("tcp", Addr)
	if err != nil { return }
	c, err := net.Dial("tcp", Addr)
	if err != nil { return }
	a, err := l.Accept()
	if err != nil { return }
	go reader(a, c)
	_, err = c.Write(make([]byte, Size)) // 32 MiB: more than loopback's socket buffers hold
	if err != nil {
		oe := err.(*net.OpError)
		if _, ok := oe.Err.(*os.SyscallError); !ok && oe.Timeout() {
			panic("tcpwritedeadline: a Write timed out, its deadline set while it ran")
		}
	}
}
```

Go (`TestMainPanics`, each run its own process, `repeat.sh`): **99 of 100, and 198 of 200, runs
panic**. In the others the new connection's `Write` fails with `ECONNRESET` (an `*os.SyscallError`:
no panic; 3 of 1500 runs of the same body): the fixed port's 4-tuple is probably reused from the
previous run's connection, which its process's exit reset. A reset is a cut, which the model
allows, so the theorem covers those runs too.

**The proof.** Translated by the pinned goose (project `nettcp`, package
`../axiomcx/tcp-writedeadline`; package init and table by `etc/gen-init.py`, `NT_PKGS`/
`NT_PROGRAMS`). `Main.lean`'s `wp_Main` is the triple `{{ isPkgInit pkg ∗ tcpPlan G addr host ∗
⌜G.plan !! addr = some host⌝ ∗ tcpPend G addr ∅ }} Main #() {{ RET #(); True }}` from the specs of
`net.Listen`, `Dial`, `Listener.Accept`, `Conn.Read`, `Conn.Write`, `Conn.SetDeadline`,
`OpError.Timeout` (all proved from the trusted models over the extension) and `time.Now.spec`. The
ghost argument (`raceInv`): the dialer's end and its direction are in an invariant that is *before
the write* (the direction empty, `wdl = false`, the reader's token `γr` inside) or *after* (the
writer's token `γw` inside, and `γr` until the reader takes it). The `Write` holds `γw`, so its step
finds *before*: no deadline, no timeout (`write_au`). A `Read` of one byte from an empty direction
returns no bytes and leaves it empty (`read_empty`), so a `Read` that returns a byte finds *after*
and takes `γr` (`read_au`); holding `γr`, the `SetDeadline` finds *after* (`deadline_au`). So the
`Write`'s error is `nil`, or an `*OpError` whose `Err` is an `*os.SyscallError` (the type
assertion succeeds) or `poll.ErrNetClosing` (whose `Timeout()` is `false`, `ErrFlag`): `Main` never
reaches the panic. `Results.lean`'s `writedeadline_safety` is the closed theorem over Perennial's
`goose_dist_adequacy` (executions without crashes, as Go's run is): from a local state with no
package initialized and its main thread, the node's host `h`, the plan with `Addr` at `h`, well
formed (`PlanWellFormed`, checked by `decide`), the network with no connection, no thread is stuck
and none has an unrecovered panic. `flock .lake/agent-build.lock lake build
NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline.Results`: built;
`#print axioms writedeadline_safety`: `propext`, `Classical.choice`, `Quot.sound`, the translation's
axiomatized types (`net.Dialer`, `net.netFD`, ..., `os.Process`, `sync.Map`, ...) and
`time.Now.wp_proof`; no `sorryAx`.

Why not the crash form (`goose_dist_crash_adequacy`, as the examples): with crashes the program is
not safe in the model either, for a reason that is not this gap (N1): a connection dialed before a
crash stays pending (D7) with the bytes its dead dialer wrote, a restarted node may accept it
instead of its own, read a byte its own `Write` did not write, and set the deadline before its own
`Write`'s step. Go's run has no crash, so the crash-free theorem is the refutation.

**What rests on it.** No example sets a deadline while another goroutine writes on the same end
(`preface` sets and clears deadlines in the goroutine that reads and writes), and no proof of the
examples mentions `wdl`, so no exported result is known to be false; but every theorem over the
extension is about a semantics with this gap.

**Proposed fixes (not applied: a trusted change, for the user).**

1. The faithful one: make `"Write"` the loop it is. `WriteStep` may append a non-empty proper
   prefix of `bs` (open direction, end not closed) and continue as `ExternalOp "Write"` of the
   rest, carrying the count so far (or the trusted `conn.Write.impl` loops over the extension's op,
   as `poll.FD.Write` loops over `write(2)`); each step's outcome is the present `WriteOutcome` on
   the current state, its count added. A timeout then needs a deadline set at the step that times
   out, as in Go, and the bytes appended by earlier steps are what the peer may already have read.
   The `Conn.Write` spec becomes a sequence of updates, so `wire.write_au` and the examples' write
   proofs change.
2. The small one: drop `st.wdl = true` from `WriteOutcome`'s three timeout clauses (a `Write` may
   time out whatever the deadline when its step is taken), and say in D2 and D5 why. Sound (it only
   adds behaviours); it loses "a `Write` on an end that never had a deadline does not time out",
   which no proof uses today (`wdl` appears only in `Impl`, `Ghost`, `Tests` and this
   counterexample).

Either way `doc.go` gets a row for `TestWriteDeadlineSetDuring` (REFUTES D2/D5, then "allowed"),
and once applied `writedeadline_safety` no longer holds: take the translation and the proof out of
project `nettcp` (`etc/goose.py`, `etc/gen-init.py`), as the v2 review's were, keeping the program
and its test. Reads need no change: a timed-out `Read` consumes nothing, so its step can be placed
after a concurrent `SetDeadline`.

### Applied (2026-11-14/15; semantics v3.1)

The first fix, the faithful one (the user's choice): a `Write` is Go's loop. `WriteOutcome` (D2) is
now one step of it, one `write(2)` with its wait, on the bytes `rs` not yet written: on a closed end
`closed`; into a shut direction `sys` or (a write deadline set) `timeout`; into an open one the
first `k ≤ |rs|` bytes appended with no failure (all, some, or none: a wait), or `sys` appending
nothing and cutting the direction, or (a write deadline set) `timeout` appending nothing; into a
cut one any `k ≤ |rs|` counted and discarded, or `sys`, or `timeout` with a deadline. The trusted
`conn.Write.impl` is the loop (`model.writeLoop`: the extension's `"Write"` of `b[nn:]` until a step
fails or `nn = len(b)`), so a timeout needs the deadline set at the step that times out, as in Go,
and the bytes of the earlier steps are what the peer may already have read. D15 is now "a `Write` is
a loop of steps": v3's clause for the `Write`/`Close` race (a prefix with `closed`, the end not
closed) is gone, the race being a `Close` between two steps (`TestWriteCloseRace` still allowed).
`TestWriteDeadlineSetDuring` is in `examples/net/semantics/write_test.go` (allowed), with its
`doc.go` row and `Tests.lean` examples (the trace step, `SetDeadline`, timing-out step; a step with
no deadline cannot time out). `writedeadline_safety` no longer holds: the counterexample's
translation and proof were taken out of project `nettcp` (`etc/goose.py`, `etc/gen-init.py`), its
program and test kept in `examples/axiomcx/tcp-writedeadline`. `net.Conn.Write.spec` is over a
writer predicate and a per-step accessor (`notes/net-tcp-v3-plan.md`, E11).

### Findings that are not refutations

- **N1. Stale pending connections across a crash** (above): the model lets a restarted node accept
  a connection dialed by its previous incarnation, with its bytes, which Linux resets (D7 says so).
  Sound, but a crash theorem cannot rely on "the connection I accepted is the one I dialed" even for
  a node that dials only its own listener.
- **N2. `CloseWrite` of a closed TCP socket.** Linux's `inet_shutdown` in `TCP_CLOSE` returns
  `ENOTCONN` and still sets `SEND_SHUTDOWN` (`fallthrough`): later writes fail with `EPIPE`.
  `CloseWriteOutcome`'s `sys` branch leaves the direction unchanged; since any later `Write` on an
  open direction may fail anyway, this is sound (the v2 review's row 15 found it by measurement).
- **N3. `TestWildcardListen` measures one order only** (a wildcard open, then the specific
  address). `examples/axiomcx/tcp-writedeadline`'s `TestListenOrders` measures both orders and the
  three spellings pairwise: every pair is `EADDRINUSE`, so D6/D21's forced failure holds.
- **N4. A fresh loopback connection can be reset at once** when a fixed port is reused across runs
  (R1's failed runs): a cut, allowed.

### Attacks that failed (v3)

| # | Attack | Outcome | Evidence |
|---|---|---|---|
| 1 | `closed` is `poll.ErrNetClosing` (`errNetClosing{}`) for `Read`, `Write`, `Close`, `CloseWrite`, `SetDeadline`, `Accept`, `LisClose` on a closed end or listener; never on one not closed | Go's: `fdmu` stays closed after `increfAndClose`; `readLock`/`writeLock`/`incref` fail with `errClosing(false)`; only `Close` evicts the poller | `internal/poll/fd_unix.go`, `fd_mutex.go`, `fd_posix.go` (`Shutdown`) |
| 2 | `timeout` is `poll.ErrDeadlineExceeded`, unwrapped (`wrapSyscallError` wraps only `Errno`) | Go's | `net/fd_posix.go`; `TestDeadlineErrors` |
| 3 | `sys` names: `"read"`, `"write"` (`fd_unix.go:18,21`), `"shutdown"` (`netFD.shutdown`), `"accept4"` (`poll.FD.Accept`'s `errcall`); `Dial`/`Listen` arbitrary | Go's | `net/fd_posix.go`, `internal/poll/sock_cloexec.go` |
| 4 | `OpError` fields per operation: `Op`; `Net` (`fd.net` is `"tcp"`, MPTCP listeners and wildcards included); `Source`/`Addr` (conn ops `laddr`/`raddr`; deadlines `nil`/`laddr`; `Accept` and the listener's `Close` `nil`/`laddr`; `Dial` `nil` (`sd.LocalAddr`) and the resolved address, also on `dialSerial`'s timeout paths; `Listen` `nil`/`la`) | Go's (`net.go:198-299`, `tcpsock.go:376-401`, `dial.go:739-810, 903`); the paths with `Addr: nil` (resolution failures) are unreachable for plan strings | source |
| 5 | `OpError.Timeout`/`Temporary`: `errNetClosing` false, `*DeadlineExceededError`/`*timeoutError` true, else arbitrary; program-built `OpError`s (`Op: "accept"` with `syscall.ECONNRESET`, a nil `Err`, an `*os.SyscallError` around a timeout) | a superset of `net.go:539-565` | source |
| 6 | Type assertions (`*OpError`, `*os.SyscallError`, `syscall.Errno`; `io.ReaderFrom` on a `*TCPConn`) | goose emits Go's full method sets (`MethodSetIs`), untranslated methods included | `NetTcp/Code/net.lean` |
| 7 | `errors.Is(err, context.DeadlineExceeded)` on a `DialTimeout` timeout | `timeoutError.Is` translated; `DeadlineExceededError` has no `Is`: both as Go | source |
| 8 | D17: `Close` of an open end or listener fails | never: `close(2)` of a socket returns 0 (no `flush`); `Close` waits for concurrent I/O (`csema`) and still returns `nil` | `poll.FD.Close`, `destroy` |
| 9 | `SetDeadline` of an open end fails | never (`ErrNoDeadline` needs an unregistered fd, which fails the `Dial` or `Accept`) | `setDeadlineImpl` |
| 10 | D15: `(k > 0, ErrClosed)`, the peer reading `k` | allowed (no precondition) | `TestWriteCloseRace` |
| 11 | A blocked `Write` and a concurrent own `CloseWrite`: `(k > 0, EPIPE)`, the peer reads `k`, then EOF | allowed: the `Write` steps first (`sys`, cut), `CloseWrite` of a cut direction succeeds, a cut direction reads its bytes then EOF | conform README (`writeclosewrite`) |
| 12 | **A deadline set during a blocked `Write`** | **refuted** (R1) | above |
| 13 | A `Read` timing out, its deadline set during it | allowed: a timeout changes nothing, so the `Read` steps after the `SetDeadline` | `ReadAvail` |
| 14 | D16: a failed `DialTimeout`'s connection accepted, reading EOF or a reset | allowed (for every dial) | `TestDialTimeoutAccepted` |
| 15 | D19: `DialTimeout`'s errors: `errTimeout` (`mapErr`; also `partialDeadline` and the `ctx.Done()` checks), `ErrDeadlineExceeded` (`WaitWrite`), `*os.SyscallError`; `errCanceled` unreachable (no cancel before return); a success leaves no deadline (`context.AfterFunc`'s `stop()` false turns a success into `errTimeout`; the deferred `SetWriteDeadline(noDeadline)` runs last) | as the model; a timeout of 0 means none (a superset) | `net/fd_unix.go:50-147`, `dial.go` |
| 16 | D18: `LocalAddr`/`RemoteAddr` nil or changing | never: `getsockname` of a TCP socket does not fail (`inet_getname`, peer 0); `accept4`'s address is AF_INET/AF_INET6; `dial`'s `raddr` falls back to the dialed one; stored once (`setAddr`), returned as stored | `sock_posix.go:136-143`, `fd_unix.go:162-163`; `TestAddrs` |
| 17 | D21: the forced failure in both orders, all spellings | `EADDRINUSE` in every pair | `TestListenOrders` (N3) |
| 18 | D21: a wildcard listener accepts dials the model routes elsewhere | only dials to a plan address with its port, unique in the plan; a plan address not on the node's machine only removes real behaviours (the real `Dial` fails) | `ListenAt` |
| 19 | Two nodes with one host string both listening at one address | the model allows the second success (more than Linux) | `ListenStep` |
| 20 | `PlanWellFormed`'s parser: leading zeros, `+`, whitespace, empty parts, extra colons, ports 0 or above 65535, `0.x`, multicast | all rejected (`decNat`, `isDigit`, `splitBy`); accepted strings are Go's canonical IPv4 literals, distinct sockets; broadcast-like addresses below 224 (`127.255.255.255`, a subnet's broadcast) only make `Listen`/`Dial` fail, which is allowed | `Deploy.lean` |
| 21 | Package facts: `ErrClosed`/`errClosed` hold `errNetClosing{}`, `errTimeout` a `*timeoutError`, `os.ErrDeadlineExceeded` is `poll`'s pointer | proved from the translated initializers (`errClosed`'s trusted one stores the zero value, as Go's `errClosed = poll.ErrNetClosing`) | `NetTcp/Proof/net/Init.lean`, `Code/os.lean` |
| 22 | Zero-size pointers (`&DeadlineExceededError{}`, `&timeoutError{}` may compare equal in Go) | unobservable: both unexported, the model reads the variables | — |
| 23 | The initial state: `initgP` (no connection), arbitrary listeners and host, the plan in the ghost state | proved; an arbitrary initial `lis` only strengthens the theorems | `Ghost.lean` |

Not tried: listener deadlines and the other unmodelled methods (stuck), IPv6-only hosts, `GODEBUG`
variations, memory exhaustion (D12).

## v3.1 (2026-11-15)

Reviewed by the `axiom` skill, adapted to a trusted operational semantics, on branch `net-tcp` at
`c0a47d0234`: semantics v3.1 (commit `b334f68554`; `notes/net-tcp.md`, "The semantics (v3.1)";
`notes/net-tcp-v3-plan.md`, E11), the same target (Linux 7.0.0-38-generic, default sysctls,
Go 1.27.3, sources read in `/usr/local/go/src`). Read whole: `b334f68554`'s diff,
`WriteOutcome`/`WriteStep` and the D2/D15 text in `Impl.lean`, `model.writeLoop`/`conn.Write.impl`
and the faithfulness paragraph in `NetTcp/TrustedCode/net.lean`, `NetTcp/Spec/net/Conn__Write.lean`,
Go's `(*poll.FD).Write` (`internal/poll/fd_unix.go:365-406`), `writeLock` (`fd_mutex.go:249`),
`(*FD).Close` (`fd_unix.go:91`), `(*netFD).Write` (`net/fd_posix.go:108`), `(*conn).Write`
(`net/net.go:204`), `convertErr` (`fd_poll_runtime.go:116`), `netpollcheckerr` (`runtime/netpoll.go:512`).

**Verdict: survives.** No program was found that panics in Go and has a no-panic proof over v3.1.
`WriteOutcome` as one `write(2)` with its wait, and `model.writeLoop` as `poll.FD.Write`'s loop,
match Go and Linux on every path of the loop (below). Six new measurements of the loop's corners
(`examples/axiomcx/tcp-writeloop`, tests only) agree with the model, and their traced runs are
ADMITTED by the conformance checker and CERTIFIED by the Lean replay. There are no refutations. The
findings below are a source-reading gap on the unchanged Read path (M1, not reproduced), checker
robustness (M3) and documentation (M4).

### What changed since the v3 review (`f0ce9973c8`)

`git diff --stat f0ce9973c8 HEAD -- GooseLang/Ext/Tcp NetTcp/TrustedCode NetTcp/Code/net.toml
NetTcp/ManualProof etc/gen-init.py etc/goose.py`, and `git log` over the same paths (two commits,
`b334f68554` and `df138a485d`):

| File | Trusted | What changed |
|---|---|---|
| `GooseLang/Ext/Tcp/Impl.lean` | yes | `b334f68554`: the version line, D2 and D15 rewritten, `WriteOutcome` (one step on the bytes `rs` not written), `WriteStep`'s docstring; no other relation changed |
| `NetTcp/TrustedCode/net.lean` | yes | `b334f68554`: the faithfulness paragraph, `model.writeLoop` (new), `conn.Write.impl` (the loop from 0) |
| `etc/gen-init.py`, `etc/goose.py` | yes | `b334f68554`: v3's counterexample (`tcp-writedeadline`) taken out of project `nettcp`; nothing else |
| `GooseLang/Ext/Tcp/Specs.lean` | no (proved) | `writeOutcome_total` restated, `writeOutcome_le`, `writeOutcome_fail`, `wp_tcp_Write`'s docstring |
| `GooseLang/Ext/Tcp/Tests.lean` | no | per-step examples |
| `GooseLang/Ext/Tcp/Decide.lean`, `Replay.lean` | no | `df138a485d`: the checker's deciders and replay; imported only by `lean_exe nettcp-replay` (`lakefile.toml`'s only change), by no proof |

Unchanged: `Ghost.lean`, `Adequacy.lean`, `Deploy.lean`, `NetTcp/Code/net.toml`,
`NetTcp/ManualProof/net.lean`, `NetTcp/Proof/net/{Base,Init}.lean`, `NetTcp/Proof/runtime/`, the
Perennial pin (`lake-manifest.json`), `lean-toolchain`. The checker's commits (`972ef939ea`,
`2089b490b6`, `df138a485d`) and the examples' re-proofs (`335173e165`, `128c3c4f81`, `040e6ce09f`,
`c5427ba5f5`, `3e7a5d43c4`, `9f1a49dd94`, `795b3d1583`) touch no trusted file. Of
`NetTcp/Spec/net/` only `Conn__Write.lean` changed. All 16 specs there have proofs in
`NetTcp/Proof/net/`, and there is no `axiom` or `sorry` in `NetTcp/Proof`, `NetTcp/Spec` or
`GooseLang/Ext/Tcp` (`PkgInitExt.lean`'s one match is a comment). So no spec can promise more than
the model. The seven examples' `Results` are up to date over v3.1 (`lake build --no-build`: all
targets up-to-date).

### The claims (v3.1)

1. A step on a closed end: `closed`, nothing written.
2. Into a shut direction (`fin`): `sys`, or `timeout` with a write deadline set; nothing written.
3. Into an open direction: the first `k ≤ |rs|` bytes appended with no failure; or `sys` appending
   nothing and cutting the direction (its unread bytes kept); or `timeout` (deadline set) appending
   nothing, the direction unchanged.
4. Into a cut direction: any `k ≤ |rs|` counted and discarded; or `sys`; or `timeout` (deadline set).
5. The loop: `b[nn:]` read at each step; `(nn, nil)` once `nn = len(b)` after a successful step;
   `(nn, err)` at the first failing step; an empty `b` takes one step, which may fail.
6. `Conn.Write.spec`'s post: `w <+: bs`, `n = len w`, `res = none → w = bs`,
   `w = bs → res = none ∨ bs = []`, and `resErr` of the last step's kind (proved from 1-5).

### Attacks

**A1. Can one `write(2)` both append bytes and fail?** No. A system call returns one value: Go's
`syscall.Write` gives `n = -1` with the error, and `(*FD).Write` counts only `n > 0`
(`fd_unix.go:380`). Linux's `tcp_sendmsg_locked` returns the count whenever it copied anything
(`do_error: if (copied + copied_syn) goto out`). An error met after copying (a reset processed from
the backlog at `restart`, a shutdown) is left in `sk_err`/`sk_shutdown` for the next call: two
steps, a success then a failure, which is what the model has. Measured
(`TestCloseDuringWrite`, `TestCloseWriteDuringWrite`, `TestTwoWritesAndClose`, 110 or more
iterations each): the peer reads exactly the `n` the failing `Write` returned, then EOF. A failing
step that appended bytes would show more.

**A2. Does the loop return exactly Go's `(nn, err)`?** Walking `fd_unix.go:365-406`:

| Go | The model |
|---|---|
| `writeLock` fails (closing): `(0, ErrNetClosing)` | the first step on a closed end: `closed` |
| `prepareWrite` fails: `ErrNetClosing` or `ErrDeadlineExceeded` (`netpollcheckerr`: closing first) | the first step: `closed`, or `timeout` (wdl set; a closed end gives only `closed`, as Go's order) |
| `write(2)` of `p[nn:max]`, `n > 0` | a step appending `k = n` (`k ≤ |rs|`) |
| `nn == len(p)`: return `(nn, err)`; `err` is nil after an `n > 0` write, the call's error for an empty `p` | `nn = len` after a successful step: `(nn, nil)`; an empty `b`: its one step's result |
| `EAGAIN`, pollable: `waitWrite`; nil: continue; else `ErrNetClosing`/`ErrDeadlineExceeded` | a `k = 0` success (a wait), or a failing `closed`/`timeout` step |
| another errno: `(nn, errno)`, wrapped `*os.SyscallError{"write", errno}` (`fd_posix.go:111`) | `sys` (`model.sysErr "write"`) |
| `n == 0`, no error, `nn < len(p)`: `(nn, io.ErrUnexpectedEOF)` | not modeled; unreachable: a nonblocking TCP `write(2)` of a nonempty buffer returns a count above 0 or an error (`EAGAIN` when full) |
| `EINTR`: retried in `ignoringEINTRIO` | unobservable |
| `EAGAIN` on a non-pollable fd: `(nn, EAGAIN)` | unreachable: a `*TCPConn`'s fd is registered (`netFD.init` failing fails the `Dial` or `Accept`: `sock_posix.go:126`, `fd_unix.go:158`), and `runtimeCtx` is cleared only in `destroy`, after the `Write`'s reference is dropped |
| `maxRW` (1 GiB) chunks | any `k ≤ |rs|`; Linux copies at most the send buffer's space per call anyway (4 MiB here) |
| `n > max-nn`: Go panics (issue 61060, VPN drivers) | Linux never returns more than asked; no step counts more (`writeOutcome_le`) |

The `waitWrite` errors are `convertErr`'s (`fd_poll_runtime.go:116`). `pollErrNotPollable` is
never one, since `netpollcheckerr` reports the event error only for `'r'` (`netpoll.go:523`; M1).

**A3. Can a step's progress exceed what Go could write?** No: `k ≤ |rs|`, and the bytes are
`rs.take k`, `b[nn:nn+k]` as `write(2)` of `p[nn:]` takes them. A model step coarser than Go's
(1 GiB+ at once) is unobservable, since a Read takes any prefix of what is unread.

**A4. Two concurrent `Write`s on one end.** Go's `writeLock` serializes them. Measured
(`TestConcurrentWritesSerialized`, 8 MiB each, 160 iterations): never interleaved. The model may
interleave their steps: extra behaviors only (sound; `notes/net-tcp.md`, "Open"). A `Write` waiting
for the lock when the end is closed returns `(0, ErrClosed)` (`TestTwoWritesAndClose`), the model's
step on a closed end. A deadline that passes while it waits for the lock is seen by `prepareWrite`
once it has the lock: a step with wdl set.

**A5. A `Write` racing with `Close`.** `poll.FD.Close` (`increfAndClose`, `evict`, then
`Semacquire(&fd.csema)` since sockets are nonblocking) returns only once the `Write`'s reference is
dropped (`writeUnlock`, deferred in `FD.Write`), so every `write(2)` of the `Write` lies within
`Close`'s interval. The model's `Close` step goes after the `Write`'s last successful `write(2)`
and before its failing wait (woken by `evict`). Measured (`TestCloseDuringWrite`): `(n, ErrClosed)`,
`0 < n < len`, `Close` nil, the peer reads `n` then EOF. (`Close` can return a few µs before the
`Write`'s caller resumes, which the test's first version wrongly asserted against, failing 1 run
in 50; only the system calls are ordered.)

Could an observer of a started `Close` force one of the `Write`'s appends after the `Close` step?
Such observers are a concurrent `Read`'s or `SetDeadline`'s `ErrClosed`. An append can always be
placed earlier, because no operation observes its absence: a `Read` of an open direction never
answers "empty" (`wait` is not a result, a `timeout` needs only rdl, EOF needs `fin`/`cut`). A
program that would make the late bytes differ, by modifying `b[nn:]` after the observation, races
with the model's loop, which reads `b[nn:]` before every step, the failing one included. It has no
proof (and is a data race in Go too: `syscall.Write`'s `race.ReadRange`).

**A6. A `Write` racing with `CloseWrite`.** `shutdown(2)` and `tcp_sendmsg` serialize on the socket
lock. Measured (`TestCloseWriteDuringWrite`): `(n, write: EPIPE)`, `0 < n < len`, the peer reads `n`
then EOF. The model: steps appending `n`, `CloseWrite` (`fin`), `sys` on `fin`. This is v3's row 11,
now allowed without a cut.

**A7. A `Write` racing with deadlines.** `netpollcheckerr` checks only the mode's own deadline. A
read deadline never times a `Write` out (`TestReadDeadlineDuringWrite`, 110 iterations: `(len,
nil)`), as the model's `DeadlineOutcome` of kind 1 leaves wdl. A write deadline set and at once
cleared gave 0 timeouts in the 120 iterations logged (320 passed: `TestDeadlineSetThenCleared`); the model allows both
outcomes. A deadline set while the `Write` blocks is `TestWriteDeadlineSetDuring`, now allowed
(v3's R1).

**A8. A `Write` racing with a reset.** The partial count first, the error at the next call (A1);
`TestPartialWriteOnReset`, the checker's `resetwrite`. Does any `write(2)` error leave a live
connection whose later bytes are delivered? That would refute the model, whose `sys` cuts the
direction and whose cut discards later bytes. On Linux TCP, no:

- `sk_err` is set on a socket that stays open only with `IP_RECVERR` (`tcp_v4_err`), which Go does
  not set. Otherwise it is set just before `tcp_done`.
- `SEND_SHUTDOWN` is permanent (`tcp_disconnect` clears it, which Go never reaches).
- A memory shortage waits (`wait_for_space`: `EAGAIN`) instead of failing with ENOBUFS.
- Accepted ends are plain TCP: Go 1.27 dials without MPTCP (`dial.go:33`,
  `defaultMPTCPEnabledDial = false`), so the MPTCP listener falls back.

**A9. `Conn.Write.spec`.** It is proved (`NetTcp/Proof/net/Conn__Write.lean`, no `sorry`), so it
cannot claim more than the model. Its post facts are Go's returns: `w = bs → res = none ∨ bs = []`
is `nn == len(p)` returning first, and `res = none → w = bs` holds because the loop's only nil
return is there. Holding `b ↦*{dq} bs` for the whole call matches io.Writer's contract.

**A10. Other paths.** `(*TCPConn).ReadFrom`, `WriteTo` and `writeBuffers` (`io.Copy`,
`net.Buffers.WriteTo`) are in `*TCPConn`'s method set, Go's, with no `MethodUnfold`, so a program
reaching them has no proof. `TCPConn.Write` is the translated promotion of `conn.Write`, and
`io.WriteString` and buffered writers go through it.

**A11. The conformance checker.** The six tests, traced (`go test -overlay`, one iteration each,
fixed ports 7181-7186) and checked: **6 of 6 ADMITTED**, all **Lean CERTIFIED**
(`check/certify.py`, `nettcp-replay` rebuilt). `TestDeadlineSetThenCleared` and
`TestReadDeadlineDuringWrite` were re-traced at 12 MiB (M3). A real run that the checker rejects
would have been a candidate; there was none.

**Re-checked from the earlier tables**, the rows that rely on `WriteOutcome`:

- v3's rows 10 (Write/Close, now A5) and 11 (Write/CloseWrite, now A6).
- v3's row 12 (R1, now allowed: `TestWriteDeadlineSetDuring`).
- v2's rows 6-11:
  - `(len, err)` still never for `len > 0`;
  - a peer reading bytes of a failed `Write`, and a `Write` after the peer's FIN or RST: allowed;
  - the empty `Write` (row 11): its one step may fail.

The other rows rely on files and relations that did not change.

### Findings that are not refutations

- **M1. Read's `ErrNotPollable` (source reading, not reproduced; Read is unchanged since v3).** The
  netpoller sets a fd's event error flag when an epoll event for it is exactly `EPOLLERR`
  (`netpoll_epoll.go:183`). It clears the flag at the fd's next event. While the flag is set,
  `netpollcheckerr` returns `pollErrNotPollable` for `'r'` (`netpoll.go:523`). So a `Read` whose
  `prepareRead` or wait falls in that window returns `*OpError{Err: poll.ErrNotPollable}`: not an
  `Errno`, not wrapped. The model's read failures are `closed`, `timeout` or `sys`, which is always
  an `*os.SyscallError`, so a program asserting `oe.Err.(*os.SyscallError)` on a read error would
  be refuted if this fired. For a TCP socket, `tcp_poll` gives `EPOLLERR` alone only when `sk_err`
  is set while the state is not yet `TCP_CLOSE`, nothing is readable and the send buffer is full.
  Without `IP_RECVERR` that is only inside `tcp_done_with_error`, between `sk_err`'s write and
  `tcp_done` (the `smp_wmb`/`smp_rmb` pair), while it purges the write queue. The netpoller must
  collect the socket's ready-list entry in that window. **Proposed (for the user):** measure it
  with a stress test (a full send buffer, the peer's reset, many concurrent `Read`s), or let a
  read's `sys` error be `poll.ErrNotPollable` too (`model.kindErr` for `"read"` choosing with
  `AnyBool`), with a D14 note. Writes are unaffected.
- **M2. Precision (sound, as `notes/net-tcp.md` lists).** Concurrent `Write`s interleave in the
  model. The model's `Close` returns at once (Go waits for in-flight I/O). A step may count 0 with
  no failure forever (Go blocks).
- **M3. The Lean replay overflows its stack on a witness with a 32 MiB step** (a 32 MiB `Write`
  read whole): `nettcp-replay` aborts ("Stack overflow detected", also under `ulimit -s
  unlimited`), and `certify.py` dies with a traceback instead of reporting the run. The same tests
  at 12 MiB certify, and a 32 MiB `Write` cut at 5.4 MB certifies. **Proposed:** byte strings in
  the replay as `ByteArray` (or tail-recursive list functions), and `certify.py` reporting a replay
  crash as a run's failure.
- **M4. `doc.go`'s "(the Write loop)" row is classed *documented*.** Its claim that a failing
  `write(2)` writes nothing is now measured (A1). **Proposed:** a row for the six tests (or moving
  them into `examples/net/semantics/write_test.go`), measured, under D2/D15. `doc.go` is the
  semantics' index and was not edited here.
- **M5. One unexplained failure.** In the first traced batch, `TestTwoWritesAndClose` printed
  `FAIL` and its output was not kept. 38 traced runs since (380 iterations) and 110 untraced
  iterations pass. The likeliest cause is v3's N4 (a fresh loopback connection reset when a fixed
  port's 4-tuple is reused), which fails the test's `Accept` or first `ReadFull`: a cut, allowed.

### Not tried

- A stress test of M1.
- A `Write` above `maxRW` (argued: A2, A3).
- IPv6-only hosts, `GODEBUG` variations, memory exhaustion (D12).

