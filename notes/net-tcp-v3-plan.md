# TCP semantics v3: what we take from dsverify-lab's network model

Started 2026-11-14 (branch `net-tcp`). The user: "Borrow the good ideas from dsverify-lab's net
semantics and add them here." The survey of dsverify-lab's `NetConn` model at its master (`91cebb8`:
`harness/lean/Harness/GooseLang/Ext/NetConn/`, `harness/netsem/`, `harness/conform/`) against ours
(v2.1, `notes/net-tcp.md`) found eleven ideas worth taking; this file is the plan and its decisions.
Every decision keeps our rules: only observable state, auditable, sound against Go 1.27.3 on Linux 7.0
(more behaviors than Linux is sound; fewer needs evidence), each decision with a Go example
(`examples/net/semantics/`).

## Decisions

- **E1. Error identities.** Errors become values a program can test, as Go's: an operation on the
  caller's own closed end or listener fails with `net.ErrClosed` (`poll.ErrNetClosing`), a deadline
  timeout with `os.ErrDeadlineExceeded` (`poll.ErrDeadlineExceeded`), a `DialTimeout` timeout with
  `net`'s `errTimeout`, and every other failure with an `*os.SyscallError` wrapping some nonzero
  `syscall.Errno` (Go's own types: dsverify-lab's model-only `connError` is refutable by a type
  assertion, so we do not copy it); each wrapped in a `*net.OpError` with Go's `Op`, `Net`,
  `Source`, `Addr`. `OpError` and `OpError.Unwrap` translated, so `errors.Is` works through
  Perennial's `errors.Is`. `OpError.Timeout`/`Temporary` are true for a deadline timeout, false for
  `ErrClosed`, and arbitrary otherwise (an `ETIMEDOUT` from keepalive or a retransmission timeout has
  `Timeout()` true: never "true only for deadlines"). The extension's results carry a kind
  (`closed | timeout | sys`), mapped to those values by the trusted `net` models.
- **E2. The Write/Close race** (dsverify-lab's F2, required by E1): a `Write` at an open end may
  return `ErrClosed` with a prefix of its bytes (shorter, or none) appended, the direction still
  open (a `Close` by another goroutine while the write blocked). Measured: `TestWriteCloseRace`.
- **E3. Abandoned dials** (F1): a failed `Dial` may leave a pending connection whose dialer's end is
  closed and whose direction from it is `fin` and empty, which an `Accept` may return (it reads EOF).
  For every `Dial` (simplest, sound). Measured: `TestDialTimeoutAccepted`.
- **E4. `Close` of an open end, and of an open listener, succeeds** (Go's `poll.FD.Close`, Linux's
  `close(2)` of a socket; `TestCloseTwice`, `TestCloseAfterReset`).
- **E5. Addresses**: a connection's `LocalAddr`/`RemoteAddr` and a listener's `Addr` are non-nil
  `*TCPAddr`s fixed at creation, otherwise arbitrary (in the Go heap: no extension state); `TCPAddr`,
  `IP` translated, `TCPAddr.String` arbitrary.
- **E6. `DialTimeout`**: as `Dial`, its failure also the timeout (E1); E3 applies.
- **E7. The deployment as a decidable premise**: `PlanWellFormed plan` (every address the canonical
  spelling of an IPv4 host that is not `0.0.0.0/8`, multicast or broadcast, with a port outside
  Linux's default ephemeral range 32768–60999 and not 0), a premise of every top-level theorem,
  checked by `decide`; the closed world stays D13's only prose assumption.
- **E8. Wildcard `Listen`** (`":p"`, `"0.0.0.0:p"`, `"[::]:p"`): resolves to the plan address with
  port `p` and this node's host, stuck unless that port appears exactly once in the plan (on one
  machine a wildcard listener takes every address with its port). Measured: `TestAddressAliases`
  extended.
- **E9. Evidence**: `GooseLang/Ext/Tcp/Tests.lean`, one `example` per `doc.go` row (the outcome
  allowed or excluded); `doc.go`'s rows classed measured / documented (a cited source) / assumed;
  tests in network namespaces (`sudo -n`, gated by `NETTCP_NETNS=1`): a partition with
  `TCP_USER_TIMEOUT` (ETIMEDOUT with `Timeout()` true, then EOF), a reset injected by the network,
  a healed partition.
- **E10. A conformance checker** (dsverify-lab's `harness/conform`): trace real runs (the examples'
  process tests, the semantics tests, a probe of races) with a `go build -overlay` tracer of `net`,
  and check each trace against a transcription of `Impl.lean` with a linearizability search; then
  certify an admitted verdict in Lean (the search outputs its witness, a `lake exe` replays it
  through decidable versions of the outcome relations, proved equivalent).

- **E11. A `Write` is Go's loop of steps** (2026-11-14, after the v3 review refuted v3's one-step
  `Write`: `notes/axiom-review/tcp-semantics.md`, R1; the user's choice of the faithful fix, v3.1).
  The extension's `"Write"` is one `write(2)` with its wait, on the bytes not yet written
  (`WriteOutcome`, D2): some bytes appended with no failure, or a failure appending nothing; the
  trusted `conn.Write.impl` loops over it as `poll.FD.Write` does (`model.writeLoop`), returning
  `(nn, nil)` once `nn = len(b)`, else the failing step's error. A deadline set or a `Close` made
  by another goroutine between two steps applies at the next one (D15, replacing E2's clause:
  `TestWriteCloseRace`, `TestWriteDeadlineSetDuring`). Into a cut direction a failure is `sys` or
  `timeout` (with a deadline), no longer `closed` (E2's departure below): `closed` needs the end
  closed, a step of its own. `net.Conn.Write.spec` takes a writer predicate `P w res` (`P [] none`)
  and a persistent accessor per step (`w ++ rs = bs`), as `wire.ReadFull`'s spec does, and returns
  `∃ w res, P w res` with `w <+: bs`, the count `len w`, `res = none → w = bs` and
  `w = bs → res = none ∨ bs = []` (an empty `b`'s one step may fail); the result index lets a
  client tie the error's kind to the failing step (shutdown's `closed`). `wire.write_au` is one step
  (each step's bytes extend the writer's `sentAll`), `wire.writeP`/`write_acc` the predicate and
  accessor for an end its thread owns.

## Phase 1 as done (2026-11-14), and where it departs from the decisions

Done: `Impl.lean` (D14-D21), `Deploy.lean`, `Tests.lean`, `NetTcp/TrustedCode/net.lean` and the
translation, the extension's and `net`'s specs and proofs, `wire`'s lemmas, `v3_test.go` and
`doc.go`. Departures, each following Go's source or a measurement:

- E1: `Dial`'s and `Listen`'s `*os.SyscallError` name is arbitrary (Go's is that of whichever call
  failed: `connect`, `getsockopt`, `socket`, `bind`, `listen`, `setsockopt`); `Read`'s, `Write`'s,
  `CloseWrite`'s (`shutdown`) and `Accept`'s (`accept4`) are Go's. `Accept` and `Dial` can also
  return a bare `Errno` (a failed `epoll_ctl` registration, `ENOMEM`/`ENOSPC`): not modeled, under
  D12. `errors.Is(err, net.ErrClosed)` has no proof: Perennial's `errors.Is` spec takes only
  pointer targets (`notes/perennial-changes.md`); `errors_Is_deadline` covers the timeout target.
- E1/E6: a `DialTimeout` timeout is `errTimeout` or `poll.ErrDeadlineExceeded` (both measured:
  `TestDialTimeoutAccepted`, and the coordinator's tracer, 413 and 355 of 768): `netFD.connect`'s
  `WaitWrite` under the write deadline it set returns the latter when the context's timer has not
  fired yet. No extension op: `DialTimeout.impl` chooses the failure's `Err` (`AnyBool`).
- E2: also into a `fin` direction a `Write` may time out (Go checks the deadline first), and into a
  `cut` direction it may fail with any kind (a timeout only with a deadline).
- E3: the abandoned connection's resources go to the `Dial` update's second branch (`wp_tcp_Dial`,
  `net.Dial.spec`), `Qfail` for both failures; `wire.dial_au`/`dial_both_au` deposit for it too.
- E5: the addresses are given read-only (`tcpAddr x`: `p ↦□ v`), and a zero `TCPListener`'s `Addr`
  panics, as Go's (nil `fd`).
- E7: `PlanWellFormed` is over the plan as a list (the extension's `GMap` is not computable), with
  `PlanWellFormed.addrOk` for the map; it excludes every address from `224.0.0.0` up (multicast,
  reserved, broadcast).
- E8: a wildcard string listens through the plan only if it is not itself a plan address
  (`ListenAt`, functional: `listenAt_unique`); the extension's ghost state carries the plan
  (`TcpGS.plan`, which the start resources name) for the uniqueness premise.
- The translation: `net` now imports the main tree's `os`, `syscall`, `internal/poll` (project
  nettcp's lean roots, as every project's), so their initializers run in `net`'s; `etc/gen-init.py`
  copies their `Init.lean` into the part (`NT_MAIN`; the main tree's import its `PkgInitExt`, which
  declares the same names as the part's). `errClosed` is a trusted initializer (`errNetClosing{}`),
  `ErrClosed` and `errTimeout` translated.

Not taken: a break that cuts both directions (ours, per direction, allows more); pending connections
owned by a listener (impossible with node-local crashes, D7); dsverify-lab's Hoare-triple token specs
(ours are logically atomic and more general); `"tcp4"`.

## Phases

1. Semantics v3 (E1–E8), the extension's and `net`'s specs and proofs, the measured tests, E9's
   `Tests.lean` and evidence classes.
2. The namespace tests (E9), in parallel with 1.
3. The seven examples re-proved over v3, `PlanWellFormed` in each theorem.
4. An axiom review of v3 (`axiom` skill).
5. The conformance checker (E10), over v3.
