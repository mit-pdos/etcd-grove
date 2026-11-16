# Our TCP semantics (v3.2) against dsverify-lab's (the final comparison, 2026-11-15)

A read-only comparison by a subagent of our semantics ("A": `GooseLang/Ext/Tcp`, v3.2 at `3213d05aa6`)
and dsverify-lab's `NetConn` model ("B": `origin/master` `a68a938`, `harness/lean/Harness/GooseLang/
Ext/NetConn/`, `harness/lean/Harness/TrustedCode/net.lean`). The earlier survey that A's v3 took ideas
from is `notes/net-tcp-dsverify-survey.md`. Paths: A relative to this repository, B to dsverify-lab, Go
to `/usr/local/go/src`. Since this comparison all seven examples are proved over v3.2 (it saw only
duplex done).

## The global state

| What it means | A | B |
|---|---|---|
| addresses the deployment may use | `plan : address → host`, fixed | `addrs : List`, fixed, no host |
| a node's identity | local `host` (Listen reads it) | local IP string (wildcard `listenAddr` reads it) |
| listeners | node-local `lis : id → (addr, open?)` | global `listeners : id → {addr, isOpen, pending : List cid}` |
| connections waiting for `Accept` | derived: `accepted = false` with that `addr` (belong to the address) | the listener's `pending` list (belong to the listener) |
| a connection | `addr`, `accepted`, two ends, two directions; numbered by a natural the semantics picks | two streams, two ends; numbered by a `w64` the semantics picks |
| a direction | unread bytes + `open/fin/cut` | unread bytes + `live/fin/cut` |
| an end | `closed`, read/write deadline set | the same |
| a crash | drops the node's listeners, keeps its host; connections stay | none in B's statement (`goose_dist_adequacy`); B's notes say a restarted node could never listen again (`notes/harness-m2a.md:152-156`), deferred to its "phase 3" |

Why listeners differ: Perennial's crash relation sees only a node's local state. B keeps listeners global
(so `Dial` can check for one and a listener's `Close` can drop its pending connections), at the price of
crashes; A keeps them local (a crash drops them), so pending connections belong to the address and `Dial`
cannot see listeners. A has `CloseWrite` (so `fin` is independent of `closed`); A breaks one direction at a
time, B both at once at any Read, Write or Close.

## Operations

| Operation | A | B |
|---|---|---|
| Dial | outside the plan: panic; else a connection, an error, or an error leaving an abandoned connection; no listener check | not configured: stuck; an error always; a connection or abandoned connection only with an open listener |
| DialTimeout | Dial's step; error `sys`, `net.errTimeout` or `ErrDeadlineExceeded` | `Dial.impl` |
| Listen | not this host's plan address (or a non-unique wildcard): panic; error only if this node has one open | configured `listenAddr` (else stuck); new only if no node has one open; listening at another node's address may succeed |
| Accept | closed: `closed`; open: error or any waiting connection to the address (or a stutter) | closed: `errClosed`; open: waits only when nothing is pending, fails, or takes a pending one |
| Listener Close | success or `closed`; waiting connections stay | same results; the pending list is dropped |
| Read | closed: `closed`; empty buffer `(0,nil)`; first k bytes; EOF on a non-open drained direction; `sys` on a cut direction (even with bytes left); timeout with a deadline; a break first | the same, but an error only once the bytes are drained; waits only on an open, empty, live stream |
| Write | Go's loop of steps; each: closed → `closed`; `fin` → `sys`/timeout; `open` → k ≥ 1 appended, or `sys` (cut), or timeout with a deadline; `cut` → discards k ≥ 1 or fails; full count with an error only for an empty buffer | one step: k ≤ len appended with success (k = len), timeout (deadline), `errClosed` at any open end, or `errBroken` plus a break; `(len, error)` for any length |
| Close | closed: `closed`; else success, outgoing → `fin` | the same after an optional break |
| CloseWrite | closed: `closed`; else `fin`, or `sys` changing nothing | not modeled (names only) |
| SetDeadline | closed: `closed`; else set unless Go's exact `IsZero` | closed: `errClosed`; "set" means `≠ time.Time{}` (a zero instant with a location counts as set: sound) |
| address getters | non-nil, arbitrary, fixed; zero `TCPConn` nil; zero listener's `Addr` panics | non-nil, arbitrary, fixed |
| errors | Go's values: `poll.ErrNetClosing` (= `net.ErrClosed`), `poll.ErrDeadlineExceeded`, `&os.SyscallError{name, Errno≠0}`, in a translated `*OpError` with Go's fields; `Timeout()`/`Temporary()` false/true/arbitrary | `Err` of a model-only type `*net#model.connError`; closed a single pointer `net.ErrClosed` is set to |
| socket options | not modeled | `SetReadBuffer`, `SetWriteBuffer`, `SetKeepAlive(Period)`: nil or an error |
| `"tcp4"` | panics (any network but `"tcp"`) | treated as `"tcp"` |
| zero values | Go's bare `syscall.EINVAL` | a nil dereference panics (sound) |
| blocking, invalid uses | every operation may stutter in every state; invalid uses panic; `isTcpStep_total` proves a non-stutter outcome everywhere | stutters only where Go waits (Read, Accept); invalid uses stuck, so specs carry progress premises |

## What one admits and the other excludes

Unsound in B (the first two measured with Go 1.27.3 on this machine):
1. `SetDeadline`'s error: Go returns `&OpError{Op:"set", Source:nil, Addr:laddr}` (`net/net.go:253`); B
   builds it with `Source = laddr`, never nil. `c.Close(); if c.SetDeadline(t).(*net.OpError).Source ==
   nil { panic }` panics every run in Go and is provably safe in B.
2. `"tcp4"`: Go's `Net` field is `"tcp4"` (`net/dial.go:903`; measured), B writes `"tcp"` in a translated
   `OpError`.
3. Likely: a deadline set while a Write blocks (A's v3 refutation R1) applies to B as is (one-step Write
   whose timeout needs the deadline at that step).
4. The model-only error type (the survey's S1), if B's goose decides the type assertion.
5. Ephemeral ports allowed by `WellFormed`: a Dial with no listener can self-connect
   (`net/tcpsock_posix.go:111,124-143`); rare.

A tighter (both sound): `errClosed` only after a Close (`internal/poll/fd_unix.go:366,394-400`); a full
count with an error only for an empty buffer; Go's exact zero time and `EINVAL`; `CloseWrite`; listening at
another node's address a proof obligation.

B tighter (both sound): concurrent Writes do not interleave (Go's `writeLock`, `fd_unix.go:366-369`; open
in A); a Dial with no listener refused and a listener's Close resetting its pending connections (A allows
more; Linux excludes them, measured); a read error only after the bytes are drained (A allows
error-then-bytes, which no measured trace shows); no two nodes listening at one address.

Open in A: `ErrNotPollable` on a read (v3.1 review, M1; by reading only); `ENOMEM`/`ENOBUFS` out of scope
(D12; B has the same gap unstated).

## Redundancy in the states

Both: ids the semantics picks; records kept forever (connections, closed listeners); bytes towards a
closed end and a closed end's deadline flags; an abandoned dial's dialer end. Only A: `addr` and
`accepted` matter only until acceptance (one `Option address` would do); a crashed node's ends. Only B:
`pending` is a list "in no particular order" (its permutations are indistinguishable); `fin` derivable
from `closed`; a closed listener's dropped connections' acceptor ends.

Can addresses be the names? B also names connections and listeners by ids it picks; even a listener,
whose address is unique while open, needs one (a closed listener's handle keeps answering `errClosed` while
a new listener works at the address); connection 4-tuples are reused within a run (both checkers saw it);
naming by address would mean modeling the kernel's port choice and reuse plus an incarnation counter, again
a name the semantics picks. What can still be removed is the dead records and unread fields above.

## Specs, proofs, evidence

A: logically atomic specs over the semantics' own pieces, each stating the outcome relation verbatim; one
Löb rule for the stutter; Write with a per-step accessor; history in a proved library (`wire/Stream.lean`);
seven small programs with crash-safety theorems (`goose_dist_crash_adequacy`); about 45 `doc.go` rows
classed measured/documented/assumed, SIGKILL process tests, namespace partitions and resets; 68
`Tests.lean` examples; three reviews (two refuted, with proved counterexamples); a conformance checker
whose verdicts are certified in Lean (21 of 22 runs, 786 mutants and 19 tampered witnesses rejected).
B: Hoare triples over ownership tokens (the writer's half of an append-only list, the reader's of a
variable, per-address protocols), errors not distinguished, `errors.Is(err, net.ErrClosed)` provable; five
real protocols proved (paxos, craq, epaxos), no crashes; `harness/netsem` on loopback, a namespace and veth;
21 `Tests.lean` examples; a hand-transcribed checker ("nothing is proved") run on 108 case-study runs under
faults (all admitted, 528 mutants rejected), which found F1–F3.

## Verdict

A better: Go's real error values; Write as Go's loop; zero values and deadlines exact; `CloseWrite`;
crashes; logically atomic specs; a checker certified in Lean; no measured unsoundness found.
B better: verified real systems, conformance on real case studies under faults; concurrent Writes
serialized; `errors.Is(net.ErrClosed)` provable; socket options; one network namespace per node.
Still worth taking from B: Go's write lock (a Write's steps not interleaving with another's); socket
options if a target needs them; A's tracer on a real system under veth/netem/iptables faults; the
`errors.Is` fix (a Perennial change). B should take from A: fix 1 and 2, Go's error types, Write as a loop.
