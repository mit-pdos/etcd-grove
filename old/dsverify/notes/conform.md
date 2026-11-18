# Conformance of real executions to the TCP model (harness/conform)

Date: 2026-11-14. Tool: `harness/conform/` (README.md there: usage, the tracer, the check, the
rule-by-rule transcription table, the tests).

## Question

The lab proves that programs are safe for every behavior of Go's `net` that the trusted TCP model
allows. The model is the extension's `NetConnStep` (`Impl.lean`) and `TrustedCode/net.lean`.
`harness/netsem` backs each of the model's decisions with a small example. Do whole runs of real
programs stay inside the model? This covers the kits' nodes as separate processes under the rig,
with and without faults. If a run leaves the model, at which event?

## Design

1. **Tracing inside Go's `net`, by `go build -overlay`.**
   - The overlay replaces `net.go`, `dial.go`, `tcpsock.go` and `tcpsock_unix.go`. The only
     change in each is that the traced definitions are renamed to `conformOrig<Name>` (31 renames,
     plus one internal call site, `newTCPConn`'s `SetKeepAliveConfig`).
   - It adds `zz_conform_trace.go`, whose wrappers take the public names.
   - Case studies and the toolchain are untouched. Go 1.27.3 supports this, but only when
     `GOMODCACHE` does not contain GOROOT: the lab's `cache/gomod` is fine, and the default
     `~/go/pkg/mod`, where the toolchain lives, is refused.
   - Traces record the API calls, so they are exactly the `net.lean` functions that the model
     interprets. Each record has the call and return times and the error's raw facts.
   - Without the overlay, the binaries are byte-identical to before. Measured: same sha256 for the
     paxos-net server node from the old and the new `rig.py`, with and without the coverage hook.
   - `rig.py` gained two generic options, `--overlay` and `--env`. Nothing else changed in it.

2. **One clock.**
   - `runtime.nanotime` is `CLOCK_MONOTONIC`. The rig's nodes are in separate network namespaces
     but in one time namespace, so their timestamps are comparable.
   - Checked on every run: all trace headers name one time namespace. Two causality checks pass:
     Accept returns after its Dial was called, and an end's operations return after the call
     that made the end.
   - The spread of the wall-minus-monotonic offset across processes is under 1 us.

3. **The decision procedure.** The trace is split into exactly independent components: one per
   bound address (listeners, Accepts, successful Dials) and one per connection (both ends). Each
   component gets an exhaustive linearization search: Wing & Gong's search with Lowe's
   memoization, over every order consistent with the real-time intervals, using the transcribed
   step relation. The hidden nondeterminism is searched, not assumed:
   - **The order of concurrent events** across processes: every order consistent with the
     intervals.
   - **When a break happened**: lazily. Section "Lazy breaks" shows this is complete.
   - **How many bytes a break lost**: lazily. A cut stream stands for the set of its prefixes.
   - **Operations cut off by process exit**: `Write`s may be linearized, appending all of their
     bytes, or left out. Other operations are left out.

4. **Error mapping and shapes** follow `net.lean`'s `connResult` and `codeErr`. The scope rules
   flag operations with no step (stuck): `U` methods, APIs that `net.lean` lacks, other networks,
   and unconfigured addresses.

### Lazy breaks: the case analysis

Write `S ≥ S'` when `S` and `S'` have equal ends, and for each stream either the two are equal,
or `S'` is cut and its bytes are a prefix of `S`'s bytes. `S'`'s "any prefix" set is then
contained in `S`'s possible futures. Let `S'` be reachable by a break before operation `o`, and `S`
by no break. The claim is that every operation allowed from `S'` is allowed from `S`, either
directly or after a break, ending in states related by `≥`:

- **Read with data `d`.**
  - From `S'`, `d` is a prefix of the cut bytes, which are a prefix of `S`'s bytes. So `S` allows
    the read too, without a break, and dropping `|d|` from both keeps the relation.
- **Read with EOF or error.**
  - From `S'`, the cut set contains the empty stream.
  - From `S`: if the stream is `fin` and empty, EOF is allowed directly. Otherwise `S` breaks at
    this Read, which `BreakOrNot` allows, and picks the empty prefix. Both sides then hold the
    empty cut stream.
- **Read timeout, zero-length Read, Read on a closed end**: the ends are equal, so these are the
  same from both states.
- **Write.**
  - `S'` cut: success discards the bytes. `S` live: success appends them, which keeps `S'`'s bytes
    a prefix.
  - `errBroken` needs a cut stream. `S` breaks at this Write first and then discards the bytes.
  - A timeout with `k` bytes appends `take k` on a live stream and discards it on a cut one. Either
    way the prefix relation holds.
  - A closed end gives the same result from both states.
- **Close.**
  - `S` live becomes `fin` while `S'` stays cut, and the bytes are unchanged. The relation holds
    because `S'` is cut.
  - Two Closes on the same end both give `errClosed`.
- **SetDeadline**: the ends are equal, so the result is the same from both states.

By induction over the rest of the linearization, a trace admitted with an early break is admitted
by the greedy rule: break only when the operation fails without a break. Every operation that
needs a break is a `Read`, `Write` or `Close` of the same connection, where `NetConnStep` allows
one. Soundness is direct: every step the checker takes is a `NetConnStep` step, and the lazy
prefix is chosen in hindsight as the bytes read before the stream's first EOF or error.

The pending-Write rule also gives the most permissive outcome. Appending all of the bytes
dominates appending a prefix, because a later break can drop the rest. No later Write of the same
end can complete while one is pending, since Go's `fdMutex` serializes Writes on an fd.

### What is proved and what is transcribed

Nothing is proved. `harness/conform/model.py` transcribes `ReadOutcome`, `WriteOutcome`,
`CloseOutcome`, `DeadlineOutcome`, `Conn.Breaks`, `BreakOrNot`, `listenAddr` and `NetConnStep`'s
eight cases by hand. Each function names its Lean definition, and the README has a table. The two
departures from a literal reading, lazy breaks and lazy prefixes, are argued above. The Lean
alternative was a decidable function over traces, proved to imply `NetConnStep` (sound) and to be
implied by it (complete, the lazy-break lemma), run as a Lean executable. It was judged too large
for this task: the linearization search, the memo, and the cross-process pairing would all need
proofs.

### Tests

- 50 unit tests (`test_conform.py`):
  - 16 hand-made positive traces that need the search (reordering, breaks, lost suffixes,
    pending Writes, reused 4-tuples);
  - real kit traces (paxos-net and craq-net under resets), admitted, with every mutant rejected;
  - real traces of `harness/netsem`'s measured examples (`testdata/`: loopback, and two private
    network namespace runs), all admitted;
  - 27 hand-made negative traces, each breaking one rule, with the finding's operation asserted;
  - 5 model unit tests.
- Mutation checks on real kit and netsem traces (`conform.py mutate`, six kinds):
  - a flipped byte;
  - a short Write with no error;
  - a Close error;
  - an EOF on an own closed end;
  - swapped Read data;
  - a Read moved before its connection existed.

  Every mutant of every kind was rejected (results below).

## Results

### Setup

- **Trees.** Scratch trees seeded with `kits/seed.py` (paxos-net fork 69b9598, craq-net fork
  c26a7f2), on this host, with the rig's `rig.toml` that kitgen generated.
- **Batches.** `batch.sh` ran 6 runs per mode, seeds 1..6, with `--ports 7000`. The modes were
  fault-free, each `gen-faults.py` kind (delay, loss, netem with jitter, reordering and
  duplication, partition, oneway, reset), mixed, and the rig's `--random`.
- **Final checker.** Every trace was checked again with the final checker.

### The kits: every trace admitted

Column key:

- **rig PASS**: the program's own verdict.
- **conns**: connection components.
- **with a break**: connections whose linearization needs a break.
- **Read errBroken** and **Write errBroken**: results of those calls with the errBroken code.

| batch (6 runs each) | conform verdict | rig PASS | conns | with a break | Read errBroken | Write errBroken |
|---|---|---|---|---|---|---|
| paxos clean | 6 ADMITTED | 6 | 166 | 80 | 0 | 0 |
| paxos delay | 6 ADMITTED | 6 | 126 | 18 | 0 | 0 |
| paxos loss | 6 ADMITTED | 6 | 142 | 52 | 0 | 0 |
| paxos netem | 6 ADMITTED | 6 | 154 | 54 | 0 | 0 |
| paxos partition | 6 ADMITTED | 6 | 150 | 37 | 0 | 1 |
| paxos oneway | 6 ADMITTED | 6 | 158 | 69 | 0 | 0 |
| paxos reset | 6 ADMITTED | 6 | 164 | 102 | 1 | 54 |
| paxos mixed | 6 ADMITTED | 6 | 126 | 50 | 0 | 26 |
| paxos random | 6 ADMITTED | 6 | 160 | 76 | 0 | 28 |
| craq clean | 6 ADMITTED | 0 | 313 | 313 | 19 | 0 |
| craq delay | 6 ADMITTED | 0 | 320 | 308 | 9 | 0 |
| craq loss | 6 ADMITTED | 1 | 314 | 309 | 2 | 0 |
| craq netem | 6 ADMITTED | 1 | 322 | 290 | 4 | 1 |
| craq partition | 6 ADMITTED | 0 | 300 | 300 | 11 | 2 |
| craq oneway | 6 ADMITTED | 0 | 315 | 315 | 3 | 0 |
| craq reset | 6 ADMITTED | 1 | 260 | 245 | 30 | 2 |
| craq mixed | 6 ADMITTED | 1 | 317 | 303 | 40 | 10 |
| craq random | 6 ADMITTED | 1 | 274 | 254 | 40 | 3 |

**Scope.** No run has an operation outside the model's scope. Neither kit calls a method that
`net.lean` lacks (no `CloseWrite`, `SetLinger` or `File`), uses `Dialer` or `ListenConfig`, or
uses an unconfigured address. That holds for craq-net too, even though real `net/http` and
`net/rpc` run there: `rpc.DialHTTP` uses `net.Dial`, `http.ListenAndServe` uses `net.Listen`,
and the CONNECT connection is hijacked before `net/http` would half-close it.

**Clock.** In every run there is one time namespace, and the wall-minus-monotonic offset spreads
across processes by under 1 us. Both causality checks pass.

**Breaks in fault-free runs.** These explain EOFs and resets at process exit, which the model
has no other way to express: a node that exits without `Close` (the rig stops the servers after
the client ends, and a crashed craq node is another case). Each `Read` timeout in craq is net/rpc
over net/http's own deadline use.

**The rig verdicts.** craq-net's FAILs are go-craq's known upstream bugs (kits/craq-net
ISSUES.md), not the network: a chain node panics on a nil neighbor in 43 of the 54 runs (R4),
and the check reports a non-linearizable history in 6. The seeded fork is upstream as released;
the kit's README results are from its dev tree.

**Mutation.** Six kinds of mutant were made, five of each, from run 1 of each batch. All 528 were
rejected:

- 90 flipped bytes;
- 90 short Writes;
- 84 Close errors;
- 84 EOFs on a closed end;
- 90 swapped Reads;
- 90 Reads moved before their connection existed.

The rig's own demo (`harness/rig/demo`, fault-free and with each of its fault files) was admitted
in 6 of 6 runs.

### Model findings: the probe

The kits' messages are small. A `Write` of a few hundred bytes never blocks midway, so it either
succeeds whole or fails before it sends anything. `harness/conform/probe` drives the patterns
where a Go `Write` is not atomic, plus one `Dial` race (README.md, "Probe"). Each pattern ran 3
times; the counts below are per run. The model was not changed for this study; it was changed
afterwards to admit F1-F3 (section "The model changed" below).

**F1. A `Dial` that failed made a connection that `Accept` returned.**

- Seen in `dialrace`, 3 of 3 runs, with 10, 13 and 16 such connections among about 34,000
  `DialTimeout` calls, 1,500 of them successful.
- Excerpt (dialrace-1):

  ```
  n1#188 Accept l1 [..242615217, ..246387926] -> conn c40 10.77.0.11:7000->10.77.0.10:53378 err=none
  no Dial returned 10.77.0.10:53378; Dials from 10.77.0.10 that failed meanwhile, e.g.
  n0#132 DialTimeout(tcp, 10.77.0.11:7000) [..236285000, ..238393556] -> dial tcp 10.77.0.11:7000: i/o timeout
  ```

- Cause: Go's connect waits for writability under the deadline. When the deadline fires, Go
  closes the socket and returns `i/o timeout`, even if the kernel has already finished the
  handshake. The listener's kernel queued the connection, and `Accept` returns it. Its first
  `Read` then sees EOF or a reset.
- It contradicts `Impl.lean`'s `NetConnStep "Dial"` (a failure leaves `g' = g`: no connection,
  nothing pending) and netsem DialListen's "Allowed: Dial failing even with a listener (backlog
  full, handshake timeout)", which does not let that failure leave a pending connection.
- Effect: a program proved against the model can assume every accepted connection has a dialer
  that holds it. In reality an accepted connection can come from a `Dial` that reported failure.
  Its stream then carries no bytes and breaks.
- One way to admit it (for the reviewers): let a failed `Dial` also add a connection, with the
  dialer's end already closed, to the listener's pending list.

**F2. A `Write` returned `(k > 0, errClosed)`, and the peer read its bytes.**

- Seen in `closewrite`, 3 of 3 runs, in 27 to 30 of about 35 Writes per run that another
  goroutine's `Close` cut short. For example, the 1 MiB `Write` returned
  `n=527072 err=use of closed network connection`, and the peer had already read 7240 of those
  bytes.
- Excerpt (closewrite-1):

  ```
  n1#6 Read c2 [..910785777, ..923434081] -> n=7240 'abcdefgh...' err=none
  other candidate: n0#3 Write c1 1048576 bytes [..922715906, ..941394076] -> n=527072 err=closed (use of closed network connection)
  ```

- Cause: `poll.FD.Write` loops over `write(2)`. When the fd is closed while it waits for buffer
  space, it returns the count written so far together with `ErrNetClosing`.
- It contradicts `WriteOutcome`'s closed case (`k = 0 ∧ code = errClosed ∧ c' = c`: nothing
  written) and netsem ErrClosed and PartialWrite, which allow short writes only with a timeout or
  a break.
- Effect: the model lets a proof conclude that a `Write` which failed with `net.ErrClosed` sent
  nothing. The peer can receive a prefix of it.

**F3. A `Write` returned `(k > 0, errBroken)`, and the peer read its bytes.**

- Seen in `resetwrite`, in 2 of 3 runs (4 Writes). Partial writes with ECONNRESET occurred in
  all 3 runs. In run 1 the peer had read none of those bytes, which the model admits.
- Excerpt (resetwrite-2):

  ```
  n0#9 Write c2 1048576 bytes [..090776134, ..120347567] -> n=569064 err=connection reset by peer = errBroken
  n1#83 Read c3 [..081392494, ..091800952] -> n=14480 'abcdefgh...' err=none     <- not admitted
  ```

- It contradicts `WriteOutcome` (`errBroken` needs `s.status ≠ live`, and on a stream that is not
  live the bytes are discarded) and netsem WriteAfterPeerClose's "Excluded: the bytes reaching a
  reader".
- The same cause as F2: Go's `Write` is many system calls, and the model makes it one atomic step
  whose error outcomes append nothing.
- One way to admit F2 and F3: an erroring `Write` appends `data.take j` for some `j ≤ k` before
  the closed or cut outcome.

**Also found by the probe: a checker bug, now fixed.** In dialrace-3, an ephemeral port was
reused. The first pairing rule took the earliest `Dial` of the 4-tuple and reported a spurious
`Read` finding. Now each `Accept` gets the latest causal `Dial`, and other pairings are searched
(README.md, "Pairing"). Tests `test_reused_four_tuple` and `test_reused_four_tuple_searched`
cover it. The verdicts above are from the fixed checker.

### The model changed (2026-11-14)

`Impl.lean` now admits F1-F3; each change has a measured netsem example.

- **F1** (netsem DialTimeoutAccepted). `NetConnStep "Dial"` has a third case: with a listener open
  on the address, a failure (`errFail`) that leaves `Conn.abandoned` pending there: the dialer's
  end closed, its stream `fin` and empty. The acceptor reads `io.EOF`, or after a break an error,
  never data. Measured on loopback: 5000 `DialTimeout`s of 1 to 60 us, 1922 failed, 1811 of those
  accepted, every one reading EOF.
- **F2** (netsem WriteCloseRace). `WriteOutcome` on an open end may return `errClosed` with
  `k ≤ len`, appending exactly the first `k` bytes to a live stream. `poll.FD.Write` returns the
  count `write(2)` took, so the appended prefix is exactly `k` bytes. The step is atomic and is
  linearized before the racing `Close`, which it cannot see: any `Write` at an open end may fail
  so (an over-approximation). On a closed end, `Write` still returns `(0, errClosed)`.
- **F3** (netsem WriteBreakPartial). `WriteOutcome`'s `errBroken` no longer needs a cut stream:
  it appends the first `k` bytes to a live stream and then breaks the connection
  (`Conn.Breaks`), which keeps any prefix. A break before the `Write`, with the bytes discarded,
  is still allowed through `BreakOrNot`.

The specs proved from `Impl.lean` (`Specs.lean`'s `wp_Write`, `wp_Dial`, `wp_Accept`, and every
spec above them) keep their statements: a writer's `W` already grew by `data.take k` for every
result, and a failed `Dial` already promised nothing. Lazy breaks stay complete: an `errBroken`
`Write` from the state without the break appends and breaks, which dominates the cut state's
discard; an `errClosed` `Write` appends on a live stream and discards on a cut one, keeping the
prefix relation. The checker (`model.py`, `checker.py`) follows the new rules: an `Accept` that
no `Dial` returned is matched with a failed `Dial` from its host. Three new probe runs are
ADMITTED (17 to 22 such accepts, 33 to 35 `errClosed` and 2 to 6 `errBroken` `Write`s per run);
the checker before the change rejects all three (F1: 17 to 22 findings; F2: 27 to 33; F3: 1 to 5).

### Limitations of this study

- 54 runs per kit and 9 probe runs, all on one host.
- The kits never reach F1 to F3. Their deadlines are long relative to the round trip (paxos's
  dial timeout is 1 s), and their messages are small. A kit with large messages, short dial
  timeouts, or a `Close` racing a blocked `Write` would reach them.
- The checker is a hand transcription, tested but not proved (README.md, "Limitations").

### The verified runs on the corrected model (2026-11-14)

The five verified net runs were rebuilt with 41a7f83's model delta (`Impl.lean`, `Specs.lean`,
`TrustedCode/net.lean`) applied to their own harness copies (`Harness/`, `etc/lab-goal/goal/fixed/`
and the goal's `fixed/`), and nothing else of the later harness: a fresh clone at `final`, the
`verify.sh` steps (build of every module, sorry check, `#print axioms`, the goal check, the
project's gates), off the machines (`bwrap` at `/home/agent/work`, Perennial 4c8617a9e prebuilt,
go1.27.3). The deltas are `theorems/RUN/model-fix-41a7f83.patch`.

No proof changed. No project file outside `Harness/` uses the generalized internals (`write_rel`,
`netCtx_dial`, `WriteOutcome`, `Conn.fresh`); the agents' proofs reach the net only through the
exported specs, whose statements 41a7f83 kept.

| Run | Delta | Build, sorry | Axioms vs `theorems/RUN/axioms.txt` | Goal | Gates |
|---|---|---|---|---|---|
| epaxos-net-1 | clean | PASS | same per theorem (union 391) | PASS | PASS |
| paxos-net-2 | clean | PASS | same (265) | PASS | PASS |
| craq-net-2 | clean | PASS | same (356) | PASS | PASS |
| craq-net-1 | clean | PASS | same (356) | PASS | PASS |
| paxos-net-1 | 2 of 12 `Specs.lean` hunks by hand (its copy predates `connFresh`) | PASS | same (265) | PASS | translation FAIL: its pin wants go1.27.1, only go1.27.3 here; passes with the version test removed. The other 4 PASS |

Not exercised: the mirror-based `lake update` (Perennial linked prebuilt at the manifests' pins);
translation gates ran on go1.27.3, not each run's pinned toolchain.
