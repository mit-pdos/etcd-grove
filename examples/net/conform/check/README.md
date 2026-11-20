# check: the conformance checker (the checking half of E10)

`../` records whole runs of real Go programs (every call of `net` they make: the tracer, its
trace format, the probe, the collection). This directory decides, for each recorded run, whether
some execution of the net extension's trusted semantics (`GooseLang/Ext/Net/Impl.lean`, with the
trusted models of `Net/TrustedCode/net.lean` that build Go's values from the extension's) produces
it, and outputs a **witness** of an admitted run that a later step replays through Lean
(`notes/net-tcp-v3-plan.md`, E10). It adapts dsverify-lab's `harness/conform` (Wing & Gong's search
with Lowe's memo, lazy breaks, lazy prefixes, components, ends paired by 4-tuple;
`notes/net-tcp-dsverify-survey.md` §2) to our model: pending connections belong to an address, a
cut is per direction, crashes are node-local, errors have kinds and Go shapes, `CloseWrite`,
D16's abandoned dials, D17, D21's wildcards, (v3.1) a `Write` that is a loop of steps, and (v3.2,
D22) waits as stutters, which leave no step.

**Nothing here is proved.** `model.py` is a hand transcription of Impl.lean, the rest is tested
(below). An ADMITTED verdict is then **certified in Lean** ("Certification in Lean"): the witness
and the run's calls replay through proved deciders of Impl.lean's own relations
(`GooseLang/Ext/Net/{Decide,Replay}.lean`, `lake exe net-replay`), so a CERTIFIED run rests on
the Lean definitions, not on this directory's transcription of them.

**The model transcribed** is Impl.lean v3.1 (b334f68554: `Write` a loop of steps, D2/D15 rewritten
after the v3 axiom review, `notes/axiom-review/tcp-semantics.md`), with `net.lean`'s
`model.writeLoop` (`conn.Write.impl`). `write_outcome` was first transcribed from that change's
working tree and checked against the commit: the same text (and v3.1 changed no other relation).
v3.2 (D22): `read_avail`'s wait and `accept_step`'s are gone (a wait is a stutter, never a
witness step: the search already listed none), and `write_outcome`'s non-failing step counts at
least one byte unless none remain (the search already never made a zero step of a non-empty
`rs`); the stutter and the panics of invalid uses are not transcribed (no traced call is one).
v3.3 (D23-D25): the write lock (`NetConn.dLock`/`aLock`, `WriteStep`'s `first`, `writeLast`) in
`model.py` and `replay.py`; in the search (`lazy.py`) a `Write` in flight holds its end's lock, so
another `Write` of the end takes no step until it ends (the "split" of overlapping `Write`s went);
`SetSockopt` (D24) transcribed, never traced (the tracer does not record socket options: their
calls are out of scope); `"tcp4"` (D23) stays out of the checker's scope, as every network but
`"tcp"` was (no traced program uses it; the checker and the Lean replay would have to follow each
socket's network into its errors' `Net`).

| file | what |
|---|---|
| `model.py` | the literal transcription of Impl.lean's relations and steps, and of Deploy.lean's `PlanWellFormed` (the table below) |
| `mapping.py` | from a traced call's result to the extension's, by net.lean: the shape rules and the error kinds |
| `lazy.py` | the search's states and steps: the model with its hidden choices taken lazily (exact: "Lazy cuts and prefixes") |
| `lincheck.py` | the linearization search (Wing & Gong, Lowe's memo; several successors, optional operations, operations of several steps, precedence) |
| `checker.py` | loading, nodes and crashes, mapping and scope, the plan, pairing, components, the searches, the report |
| `replay.py` | the witness: the components merged into one linearization, made concrete, replayed through `model.py` |
| `trace.py` | reads trace directories and `.tar.gz` samples (the format of `../README.md`) |
| `conform_check.py` | the command (`--calls-out`: the calls file the Lean replay reads) |
| `mutate.py` | the mutation check: mutants of real runs, each of which must be NOT ADMITTED |
| `tracebuild.py` | hand-made traces in the tracer's format, for the tests and the mutants |
| `test_check.py` | the tests; `check_test.go` runs them under `go test` |
| `certify.py` | the certification: every admitted run's witness replayed in Lean, and the negative tests; `certify_test.go` runs it under `go test` |

## Running it

```
cd examples/net/conform
python3 -B check/conform_check.py check testdata/echo-TestProcesses.tar.gz          # one run, its verdict and findings
python3 -B check/conform_check.py check -v --witness /tmp/w /tmp/net-collect/traces/probe/writeclose
python3 -B check/conform_check.py table /tmp/net-collect/traces [--json rows.json]  # every run under a directory
python3 -B check/conform_check.py mutate testdata/*.tar.gz [-n 5]                       # every mutant must be rejected
python3 -B check/test_check.py                                                          # the tests (about 15 s)
python3 -B check/certify.py [PATH...]          # certify in Lean (default: the sample; needs `lake build net-replay`)
cd examples && go test ./net/conform/check                                              # the same, from Go
```

Python 3 (3.8 or later), the standard library only. `PATH` is a run directory, a directory of
them (every directory with `.jsonl` files is a run), or a sample `.tar.gz`. `--plan FILE` gives the
plan (a JSON list of `[address, host]` pairs, hosts being node names) instead of inferring it.
`check` exits 2 if a run is NOT ADMITTED.

**Verdicts**, per run:

- **ADMITTED**: every component has a linearization the model allows, the witness replays through
  `model.py`, no shape or clock problem, nothing out of scope.
- **NOT ADMITTED**: some operation fits no execution (the first one no linearization admits, and
  why), or a Go value net.lean cannot build (shape), or the clocks are not comparable, or (a
  checker bug) the witness does not replay.
- **OUT OF SCOPE**: no such finding, but the run has operations the model has no step for
  (unmodeled APIs, non-plan addresses, port 0, an ill-formed plan, zero-value sockets); the rest is
  checked all the same, a component that fails only with out-of-scope operations in it is
  *inconclusive*, and if every component passes the witness is still built (for the extended plan).

## From traces to the model

**Results** (`mapping.py`, net.lean's `model.kindErr`, `model.connErr`, `model.errFlag`, each
model's `*.impl`): `err` null is success; `io.EOF` (unwrapped, `eof` true) is the Read result EOF,
from Read only, with no bytes; every other error must be a `*net.OpError` with Go's `Op`
(`read`, `write`, `close` for Close and CloseWrite and a listener's Close, `set`, `accept`, `dial`,
`listen`), `Net` `"tcp"`, `Source` nil for SetDeadline, Accept, a listener's Close, Dial and Listen
and the conn's non-nil `*TCPAddr` otherwise, `Addr` a non-nil `*TCPAddr`; its `Err` gives the kind:
`poll.errNetClosing` is `closed` (Timeout and Temporary false, `errors.Is ErrClosed`),
`*poll.DeadlineExceededError` is `timeout` (both true), `*os.SyscallError` with a nonzero errno is
`sys` (Timeout, Temporary arbitrary; `Syscall` Go's: `read`, `write`, `shutdown`, `accept4`, `close`,
`set`, arbitrary for Dial and Listen). For DialTimeout, `*net.timeoutError` and
`*poll.DeadlineExceededError` (both Timeout/Temporary true) are the extension's `sys` failure
(`DialTimeout.impl`'s `AnyBool` branches); a plain Dial's deadline error is the extension's
`timeout`, which `DialStep` never returns: NOT ADMITTED. A Read with an error returns 0 bytes; a
Read of `n > 0` bytes returns at least one. Anything else is a shape finding.

**Addresses** (D18): every `LocalAddr`, `RemoteAddr`, listener `Addr`, and every new socket's
addresses must be non-nil `*TCPAddr`s. "Fixed at creation" is the model's pointer identity, which
the trace does not record; the strings may differ (net.lean's `TCPAddr.String` is `AnyString`), so a
changed string is a warning, not a finding.

**Scope** (no step in the model): `Unmodeled` APIs (a socket they touch makes its component
inconclusive if it fails; one they make is out of scope with its operations); operations on `nil` or
`u` sockets; networks other than `"tcp"`; Dials and Listens of addresses no plan can have (not a
canonical `a.b.c.d:p`: `localhost:...`; their connections are left out of the check, and an Accept
of one is left out of its address's: it changes nothing the others see); a Listen whose
`ListenAt` has no address (a wildcard whose port two plan addresses share); port 0 (checked as a
Listen of the address the kernel gave it, as if the plan had it); a plan not `PlanWellFormed` (D20:
an ephemeral port, port 0; checked under it all the same).

**The plan** (D13): `--plan`, else inferred: each Listen's canonical address (resolved, for port 0)
at the host of the node that listened there (two nodes listening at one address: out of scope),
each Dial's canonical address (if no node listens there, at a host no node has), each wildcard
Listen's port resolved to the plan's only address with it (or `127.0.0.1:p` if none). Hosts are
node names.

**Nodes and crashes** (D10, D11): a node is a `node` name; its processes, ordered by their headers'
start times, are its incarnations when each ended (its driver's `exit` event, else its last record)
before the next started; processes of one name that overlap are distinct nodes with the same host
(the semantics run's test binary and its children). Between two incarnations the node crashes:
its listeners vanish, its connections stay. In the search the crash is an operation of the address
components at its host, after every operation of the old process (precedence) and before every
operation of the node's later ones (precedence too), its interval from the old process's death
bound (its `exit` event, else the next's start) to the next's start. A record after its process's
`exit` event is a clock finding (and the crash then cannot be placed: NOT ADMITTED). Operations
cut short by the end of their process (a `B` with no `E`) may take effect before its death bound,
or not at all.

**Pairing.** A Dial's new socket `(local, remote)` is an Accept's `(remote, local)`. Each Accept, in
the order they returned, takes the latest Dial of its 4-tuple that was called before it returned and
not taken (a 4-tuple names one connection at a time; ephemeral ports are reused). An Accept no Dial
pairs with is a connection no traced Dial returned: a failed Dial's (D16) or an unfinished Dial's
(below). *This fixes the model's choice of which connection an Accept returns to the one the
kernel's addresses name*: the model's addresses are arbitrary (D18), so an execution in which an
Accept returns another pending connection also exists in the model; the checker does not search
those, and a NOT ADMITTED verdict means "by no execution in which each Accept returns the
connection with its 4-tuple". (No real run is NOT ADMITTED.)

## Components

The model's global state is a product of independent parts, and so is the trace (dsverify-lab's
decomposition, adapted):

- **an address** `a0` of the plan: the listeners at it of the nodes whose host is `plan[a0]` (each
  node's `NetLocal.lis` restricted to `a0`), and the `accepted` flags of the connections dialed to it;
  its operations are the Listens resolving to it (`ListenAt`), the Accepts and Closes of those
  listeners, the Dials of it, and the crashes of its host's nodes;
- **a connection**: its two ends and two directions; its operations are the Reads, Writes, Closes,
  CloseWrites and SetDeadlines of its two ends.

No step reads two parts: `AcceptStep` reads the listener and the address's connections' flags,
`DialStep` adds a connection (pending at its address, its ends and directions fresh), the end
operations read one connection. A connection's operations come after the Dial or Accept that made
its end (program order; real time in the trace). So a run is admitted iff every component is (under
the pairing): a linearization of each, respecting real time, merges into one (README "The
witness"), and a model execution projects onto each.

## The search (`lincheck.py`)

Wing & Gong's search with Lowe's memo, as porcupine and dsverify-lab do it: walk the calls and
returns in time order; any call before the first return of an operation not done may be linearized
next; reaching such a return, backtrack; a (done set, state) pair seen before is not explored again.
`a` precedes `b` iff `a`'s return is before `b`'s call, strictly (ties are concurrent). Generalized:
a step has several successors; an operation may be optional (cut short by its process's end: its
"return" is its process's death bound, or none; it may be dropped); a successor may be partial (the
operation is not done: a Write's steps); an operation may have predecessors (a crash). The failure
reported is the operation whose return could not be passed at the deepest point of the search, with
its step's reason there, the state, the linearization up to there and the other candidates.

## A Write is a loop of steps

Go's `poll.FD.Write` loops: `write(2)` of what is left (waiting when the buffer is full); net.lean's
`conn.Write.impl` is that loop over the extension's `"Write"` steps (`WriteOutcome`: one step, of
the bytes `rs` not written yet, adding `k`; D2, D15). A traced `Write` that returned `(n, err)` is
therefore progress steps adding up to `n` (into an open direction they append, into a cut one they
discard) and, if `err` is not nil, a failing step (it appends nothing): `closed` needs the end
closed at that step (a Close of another goroutine between two steps), `timeout` the write deadline
set at that step, `sys` an open direction (which it cuts), a shut one or a cut one. Success needs
`n = len(b)`, a failure `n < len(b)` (or an empty `b`); an empty Write takes one step.

Lazily (`lazy.write`), the progress is one step (all that is left of `n`), at any point of the call
before its failing step. That dominates splitting it: a step's only effect is to append (or
discard) bytes, which the peer's Reads can only see more of, a later cut keeps any prefix of, and
the writer's other operations (Close, CloseWrite, SetDeadline) do not read; the order of the bytes
is the only thing a split changes, and only another Write of the same end could put bytes between
two of its steps, which the write lock (v3.3, D25: Go's `fdMutex`) excludes: a Write in flight
(between its first step and its last) holds its end's lock, and another Write of the end takes no
step meanwhile (`lazy.lock_holder`; before v3.3 the search tried every split of overlapping Writes).

## Lazy cuts and prefixes: why the lazy search is exact

The model's hidden choices for a connection are *when a direction is cut* (at a Read of it by its
reader, ReadOutcome's second disjunct; at a Write step that fails `sys` into it) and *how many unread
bytes a cut keeps* (ReadOutcome's `∃ k`). The lazy model (`lazy.py`) takes neither eagerly. A lazy
direction is `(B, σ, a)`: its bytes, its status, and, for an open or fin direction, `a`, the number of
bytes appended since its reader's last *cut point* (a Read of `n > 0` bytes at an open end: the only
Reads where ReadOutcome may cut), or `⊥` if it has had none. It stands for the set of model
directions

- γ(B, cut, ·) = { (P, cut) : P a prefix of B } (a cut direction stands for every prefix of its
  bytes: a later Read may cut it again, keeping any prefix, as ReadOutcome's second disjunct applies
  to a cut direction too);
- γ(B, σ, ⊥) = { (B, σ) } for σ open or fin;
- γ(B, σ, a) = { (B, σ) } ∪ { (P, cut) : P a prefix of B[0, |B| − a) }: the direction as it is, or cut
  at its reader's last cut point keeping every byte it had then, the bytes appended since discarded.

A lazy connection (its ends exactly, two lazy directions) stands for the product. **Lemma
(exactness).** For every operation o with an observed result r, the model states the model's step
(with every hidden choice) reaches from γ(ĉ) are exactly the union of γ over the lazy successors of
ĉ. By cases (the reader is the end the direction goes to, the writer the other; s is the operating
end):

- **Read, n > 0, at an open end**, of d = (B, σ, a) (a cut point: every successor has a = 0):
  - bytes x (a prefix of B, 1 ≤ |x| ≤ n): from (B, σ) ReadAvail gives (B∖x, σ), a cut first gives
    every (Q, cut) with Q a prefix of B∖x; from a retro member (P, cut), x must be a prefix of P and
    gives prefixes of P∖x, a prefix of B∖x. The union is γ(B∖x, σ, 0) (γ(B∖x, cut) if σ is cut).
    If x is not a prefix of B, none (no member has it as a prefix of its bytes).
  - EOF: from (ε, fin), ReadAvail gives (ε, fin), a cut (ε, cut); otherwise only a cut keeping
    nothing, (ε, cut); retro members give (ε, cut). So γ(ε, fin, 0), or γ(ε, cut).
  - sys: a cut keeping any prefix (or, cut already, as it is): γ(B, cut).
  - timeout (with the read deadline): (B, σ) and its cuts: γ(B, σ, 0).
  - `closed` at an open end: none. A wait has no record.
- **Read at a closed end, or of 0 bytes**: ReadOutcome's first two branches: the state as it is, no
  cut (not a cut point: `a` unchanged).
- **A Write step**, at the writer's end, open, of d = (B, σ, a), adding k of rs or failing:
  - σ open, progress k: (B·rs[:k], open); the retro members are cut, and a cut direction allows the
    same progress, discarding it: γ(B·rs[:k], open, a + k) (the retro prefix B[0, |B| − a) is
    unchanged). A sys failure: (B, cut) ⊇ the retro members' successors: γ(B, cut). A timeout (with
    the deadline): γ(B, open, a).
  - σ fin: (0, sys) and (0, timeout) keep (B, fin) and the retro members: γ(B, fin, a). A step with no
    failure (progress, or an empty Write's one step) is allowed only into a cut direction: from the
    retro members only, so γ(B[0, |B| − a), cut) if a ≠ ⊥, none if a = ⊥.
  - σ cut: discarded, the same results allowed: γ(B, cut).
  - `closed` at an end not closed: none (only a closed end fails `closed`); at a closed end, every
    step fails `closed`, unchanged.
- **Close, CloseWrite** of the writer: shut maps open to fin and keeps the others; the retro members
  are cut and stay cut: γ(shut(d)) with `a` kept. CloseWrite's sys: unchanged.
- **SetDeadline**, and the operations of the other end on the other direction: ends only.

The ends are determined by the operations (no hidden choice) and equal across γ. **Theorem.** For a
connection component, the lazy search admits it iff the model does. *Proof.* By the lemma and
induction over any order, the set of model states the order's prefix reaches with the observed
results is the union of γ over the lazy states the search reaches by the same order; it is nonempty
iff a lazy path exists. The search tries every real-time order (and every split where one is
needed), and Lowe's memo only skips (done set, state) pairs whose futures it has explored.
Soundness is also checked directly: every admitted run's witness replays through `model.py`.

**The corner** (the survey's A4): after a cut, CloseWriteOutcome keeps `cut`, so a Write after the
end's own CloseWrite may succeed, while from `fin` it cannot. Lazily: the CloseWrite makes (B, fin, a);
the Write's progress step is admitted from the retro member, which exists iff the reader had a cut
point before (`a ≠ ⊥`), and the direction becomes (B[0, |B| − a), cut). It is exact by the lemma's fin
case: a cut that is not at a cut point of the reader is a Write step's sys failure, which keeps
`cut` and is in the state anyway. The latest cut point is the best: a cut at an earlier one keeps a
prefix of what a cut at a later one keeps (the bytes read in between were there at the earlier one),
and only Reads at cut points consume bytes, so none were consumed since the latest. In the
witness, that Read is marked to cut, keeping every byte (`replay.py`, "retro cuts"). Go never does
this (its Write after CloseWrite fails with EPIPE), and no real run needed it (`retro` 0 in every
row below); `test_check.py`'s corner tests and corner histories exercise it.

**Calls cut short** (a process killed, or exited, with a call in progress): optional, before the
process's death bound. Their result is unobserved; the lazy successors are:

- a Read: a sys failure (a cut keeping everything), and, with the deadline, a timeout (a cut point,
  nothing read), and EOF of an empty fin direction; and, if another Read of the same end may still be
  linearized, each count of bytes it could have read (exact). Without one, the sys cut dominates
  every outcome: the remaining operations on that direction are then the writer's, and from a cut
  direction a Write step allows every result any state allows;
- a Write: every byte (it finished); all but the last and a sys failure (a cut); with `split`, each
  partial step (then dropped anywhere: it stopped there). Without another Write of the same end to
  come, every byte dominates any prefix: the peer can only read more, and cut to any prefix;
- a Close, CloseWrite, SetDeadline: its effect (CloseWrite's sys is the state as it is);
- dropped, in every case.

**Accepts no Dial returned.** In an address component, a connection a failed Dial left (D16, `NetConn.
abandoned`) or an unfinished Dial made (it may have succeeded) is an anonymous *token*: a failed
Dial always leaves one (more pending connections constrain nothing: an Accept may take one or not,
nothing needs one absent), an unfinished one too, and an Accept that no Dial returned takes one.
Tokens are interchangeable: each is taken by at most one Accept, and the connection component of such
an Accept has only its acceptor's operations, whose outcomes are the same from `NetConn.abandoned`
and `NetConn.fresh` (the up direction, ε fin or ε open, gives a reader the same results: EOF, sys,
timeout, no bytes; the down direction is fresh in both). An Accept left unfinished, or a Listen, is
dropped (leaving a connection pending, or a listener closed, dominates). The witness gives each such
Accept the first token of its address in witness order, and turns the tokens no Accept took back
into plain failures (or leaves the unfinished Dials out).

## The witness

Each component's linearization gets points: an operation's (or a Write step's) point is the
latest call time of it and of every step before it in that linearization (a point in its interval,
non-decreasing along it). The witness is every component's steps sorted by point (an address's
before a connection's at the same point), with each node's crashes at its old process's death
bound plus 1 ns (after every step of the old process, at or before the next's start). That order
respects real time and every component's order, but for crashes against Dials of other nodes,
which commute. It is then made concrete (a Read cuts only when its result needs it: EOF of a
direction with bytes or open, keeping nothing; sys of one not cut, keeping every byte; or when
marked: a retro cut) and replayed through `model.py`: every step must satisfy `model.net_step` (on a
one-connection `NetGlobal`: no step reads or writes another connection) or `model.crash`.

**The format** (`--witness DIR` writes `<run>.witness.json`), version 1:

```
{ "format": "net-witness", "version": 1, "run": "<the run's path>",
  "plan": [["127.0.0.1:7101", "server"], ...],      // the plan (Impl: NetGlobal.plan), as a list
  "plan_well_formed": true,                          // Deploy.lean's PlanWellFormed of that list
  "nodes": [{"node": "server", "host": "server", "procs": [pid, ...]}, ...],
  "conns": 12,                                       // connections numbered 1..conns (Impl: NewConn)
  "retro_cuts": 0,                                   // Reads marked to cut (the corner)
  "steps": [ <step>, ... ] }                         // the linearization, in order
```

A step has `i` (its index), `t` (its point, ns), `node` (the node it is a step of), `op`, and, for a
traced call, `trace: {pid, s}` (the call's records) and `pending: true` if the call never returned
(its result is then the checker's choice). The extension's argument and result, by `op`
(Impl.lean's `NetStep` cases; codes are `errCode`: 0 success, 1 closed, 2 timeout, 3 sys, and 4 a
Read's EOF):

| `op` | arguments | `res` | Lean |
|---|---|---|---|
| `Listen` | `addr` (the string passed), `a0` (`ListenAt`'s plan address) | `{code}`; on success `lis` (the listener id) | `ListenStep` |
| `Accept` | `lis` | `{code}`; on success `conn` (its number) and `end` (`endId conn true`) | `AcceptStep` |
| `LisClose` | `lis` | `{code}` | `LisCloseOutcome` |
| `Dial` | `addr` | `{code: 0, conn, end}`, `{code: 3}` (no connection), or `{code: 3, abandoned: conn}` (D16) | `DialStep` |
| `Read` | `conn`, `side` (0 the dialer, 1 the acceptor), `end` (`endId`), `n` | `{code}`; for bytes `k` (ReadAvail's `k`, their count) and `data` (hex); `cut`: null, or `{keep}`, the prefix the cut keeps (ReadOutcome's `∃ k`) | `ReadStep` |
| `Write` | `conn`, `side`, `end`, `data` (hex: the bytes not yet written, `rs`), `part` (the step's number in its call), `last` | `{k, code}`: the count the step adds, its code | `WriteStep` |
| `Close`, `CloseWrite` | `conn`, `side`, `end` | `{code}` | `CloseStep`, `CloseWriteStep` |
| `SetDeadline` | `conn`, `side`, `end`, `kind` (0 both, 1 read, 2 write), `set`, `wall`, `ext` (`(1, 0)` set, `(0, 0)` cleared: `timeIsZero`) | `{code}` | `SetDeadlineStep` |
| `Crash` | `node`, `between: [old pid, new pid]` | | `net_semantics.crash` |

Listener ids are numbered from 1 per node (never reused; Impl's `l ≠ 0 ∧ L.lis !! l = none`). A
Write call is one `Write` step per step of its loop; the call's count is the sum of its steps' `k`,
its error the last step's. Waiting (a Read or Accept that waits, a Write step that writes nothing yet)
is the model's stutter (D22), which changes nothing and is not listed. The replay checks the steps through `model.py`;
the Lean replay checks them through proved deciders of Impl.lean's relations, and against the run's
calls (next section).

## Certification in Lean

`net-replay WITNESS CALLS` (`GooseLang/Ext/Net/Replay.lean`, its `main`; built by
`lake build net-replay`, at `.lake/build/bin/net-replay`) replays a witness against Impl.lean's
definitions themselves and against the run's traced calls, and prints `CERTIFIED`, or
`NOT CERTIFIED: step i: why` (or the plan, or a call, for failures that are not one step's); it
exits 0 or 1. `certify.py` runs the whole chain:

```
lake build net-replay                                           # from the repository's root
cd examples/net/conform
python3 -B check/conform_check.py check --witness DIR --calls-out DIR RUN...   # DIR/<run>.{witness,calls}.json
.lake/build/bin/net-replay DIR/<run>.witness.json DIR/<run>.calls.json      # (from the root)
python3 -B check/certify.py [PATH...] [--out DIR] [--json rows.json]          # the checker, the replay, the negative tests
```

**The calls file** (`--calls-out DIR` writes `<run>.calls.json`; `conform_check.calls_json`), version
1: the run's records as the tracer wrote them, nothing mapped:

```
{ "format": "net-calls", "version": 1, "run": "<the run's path>",
  "procs": [{"pid", "node", "t0", "t1", "timens", "exit": <its driver's exit event's t, or null>}, ...],
  "drivers": [{"pid", "node", "timens"}, ...],
  "calls": [{"pid", "b": <the B record>, "e": <the E record, or null if the call never returned>}, ...] }
```

**What the replay checks**, in one walk over the witness's steps (the first failure is reported):

- **(a)** the plan is `PlanWellFormed` (Deploy.lean), decided (`planWellFormedB`).
- **(b)** from the initial state (the network of the plan with no connection; each witness node with
  its host and no listener), each step is a step of the model, decided on the state the replay
  threads: the connections (pending, accepted, D16's abandoned ones) and each node's listeners
  (cleared by a `Crash` step). The step's hidden choices are the witness's (a `Dial`'s connection
  number, a `Listen`'s listener id and plan address `a0`, a `Read`'s cut `keep`); the state after is
  computed from them and the relation decided on it: `ListenAt` and the new listener (`ListenStep`),
  the pending connection at the listener's address (`AcceptStep`), `NewConn` (`DialStep`),
  `ReadOutcome`, `WriteOutcome`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`,
  `LisCloseOutcome`, `IsEnd` (`Replay.step`).
- **(c)** every traced call is linearized: every call is in scope (no `Unmodeled` API, no `nil` or
  `u` socket, network `"tcp"`); every call that returned has its steps (one, or a `Write`'s loop:
  step `part` j's `data` is the call's bytes from the count written so far, `b[nn:]`; every step but
  the last has code 0 and leaves bytes to write; the last fails or writes the rest, and `last` says
  so); a call cut short by its process's end has steps or not; each step lies in its call's
  `[B.t, E.t]` (`E.t` unbounded if pending, and `pending` says which); the steps are in `t` order;
  each step is of its process's node (the witness's `nodes`, each node's processes its incarnations:
  every traced process in exactly one node, its header's node name the node's host, each ended, by
  its exit event or its last record, before the next one's header `t0`), while that process is the
  node's current incarnation; each `Crash` is between two
  consecutive incarnations, after the old one's last record and by the new one's start. One clock:
  every process and driver in one time namespace, and no record after its process's exit event.
- **(d)** each step's arguments and results are the trace's, by the mapping of "From traces to the
  model", here in Lean over the raw error facts (`Replay.errKind`, `Replay.expect`, as `mapping.py`'s
  `err_kind` and `map_call`, the shape rules included: any value net.lean cannot build refuses
  certification): a Dial's and a Listen's address, a Read's `n`, a SetDeadline's kind and
  `IsZero`, the bytes read and their count `k`, a Write's count (the steps' sum), every result code
  (error kinds, EOF), the success of an Accept, Dial or Listen; and the sockets: every operation on
  a connection or listener is a step on the end (connection and side) or listener the step of the
  call that made the socket returned. The accepted connection is thus the one the model's Accept
  returned (a pending one at the address), whatever its 4-tuple: the model's addresses are arbitrary
  (D18), and the checker's pairing by 4-tuple is not trusted.

**What is proved** (`Replay.lean`, `checkSteps_sound`; `main` runs `checkSteps` for (a) and (b)):

```
theorem checkSteps_sound [GooseExts] [GoGlobalContext] {plan nodes ss w'}
    (h : checkSteps plan nodes ss = .ok w') :
    PlanWellFormed plan ∧
    Exec ⟨GMap.ofList plan, ∅⟩ (fun n => (alGet nodes n).map (fun host => ⟨host, ∅⟩))
      (ss.map (fun s => s.op.toEv s.node)) w'.global w'.loc
```

`Exec g loc evs g' loc'`: the events `evs` in order, each a step of the model from the state the
earlier ones reached (`MStep`): `net_semantics.step` (`NetStep`) of the event's operation, argument
and result at its node's local state, for every heap, the other nodes unchanged; or the node's
`net_semantics.crash`. `WOp.toEv` is the event a witness step stands for: the extension's
operation, the argument the trusted model passes it (`PairV (#e) (#n)` for a Read, ...) and the
expression it steps to (its result value). The proof is `step_sound` per step, from the deciders'
lemmas (`GooseLang/Ext/Net/Decide.lean`) and the replay's association lists standing for the
model's `GMap`s (`World.global`, `World.loc`, `ofList_alSet`). The deciders, each with its proved
`= true ↔` lemma against the relation of Impl.lean or Deploy.lean (an existential decided at the
instance the witness gives):

| decider | relation | existentials |
|---|---|---|
| `readAvailB` | `ReadAvail st d n r d'` | `∃ k`: the count of the bytes `r` returns |
| `readOutcomeB` | `ReadOutcome st d n r d'` | the cut's `∃ k`: `cutKeep r d'`, its only candidate (`cut_unique`) |
| `writeOutcomeB` | `WriteOutcome st d rs k res d'` | none (`k` the step's) |
| `closeOutcomeB`, `closeWriteOutcomeB`, `deadlineOutcomeB`, `lisCloseOutcomeB`, `isEndB` | `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`, `LisCloseOutcome`, `IsEnd` | none |
| `listenAtB pl host a a0` | `ListenAt (GMap.ofList pl) host a a0` | `∃ p`: `wildPort a`; its `∀ x` over the plan list |
| `planWellFormedB` | `PlanWellFormed` | none (it is a `Bool` equation) |

Their atoms avoid walking a direction's megabytes where they can (`lenGe`, `appendEqB`, and
`bytesEqB`, equal at once when the two lists are the same object: Lean's `withPtrEqDecEq`, a
`Decidable` instance like any other).

**What is checked but not proved**: (c) and (d), `Replay.checkCalls`, a direct program over the
witness and the calls (its checks are the list above, each with its message). **What stays
trusted**: the tracer (each record is what Go's `net` did, `[B.t, E.t]` contains the call, one
monotonic clock); `trace.py`'s reading of the files and `calls_json`, which copy the records; the
mapping's rules (`errKind`, `expect`: a transcription of how net.lean's trusted models build Go's
values, read backwards, as `mapping.py`'s; and that a `SetDeadline` of a zero time is the trace's
`set` false, the step's `(wall, ext)` standing for the time's two words); that a node's processes,
by name and in time order, are its incarnations with a crash between each two (drivers' exit
events, else a process's last record); Lean's compiler and runtime and `Lean.Json`. Not trusted: the
checker's search, its lazy model, `model.py`, `replay.py` and its pairing by 4-tuple: a wrong
witness is NOT CERTIFIED. A certified run is ADMITTED and wholly in scope; an OUT OF SCOPE run is
not certified (its unmodeled calls refuse it).

**Results** (2026-11-15). The sample (`../testdata`, 14 runs): 14 CERTIFIED, about 14 s of Lean in all
(`certify.py`, 17 s with the checker). The collection (`/tmp/net-collect`, 22 runs, regenerated
as `../README.md` says): 21 CERTIFIED, the 22nd (`semantics/all`) OUT OF SCOPE with no witness (one
of its components is inconclusive); about 67 s of Lean in all, 80 s with the checker. The probe's runs
dominate: their witnesses list a 1 MiB `Write`'s remaining bytes at each step and their directions
hold megabytes (the buffers filled), whose `List w8` the steps copy (a write appends):

| run | steps | witness MB | calls MB | Lean s | read / steps / calls ms |
|---|---|---|---|---|---|
| acceptloop/TestProcesses | 170 | 0.0 | 0.1 | 0.11 | 7 / 1 / 2 |
| acceptloop/TestServerCrashes | 830 | 0.1 | 0.3 | 0.15 | 37 / 2 / 7 |
| duplex/TestProcesses | 182 | 0.0 | 0.1 | 0.11 | 8 / 0 / 2 |
| duplex/TestServerCrashes | 836 | 0.2 | 0.3 | 0.14 | 34 / 3 / 7 |
| echo/TestProcesses | 179 | 0.0 | 0.1 | 0.11 | 8 / 1 / 2 |
| echo/TestServerCrashes | 934 | 0.2 | 0.3 | 0.15 | 35 / 3 / 8 |
| framed/TestProcesses | 389 | 0.1 | 0.1 | 0.13 | 19 / 1 / 4 |
| framed/TestServerCrashes | 1928 | 0.4 | 0.6 | 0.18 | 66 / 6 / 13 |
| halfclose/TestProcesses | 120 | 0.0 | 0.0 | 0.11 | 5 / 1 / 1 |
| halfclose/TestServerCrashes | 636 | 0.1 | 0.2 | 0.13 | 24 / 2 / 5 |
| preface/TestProcesses | 229 | 0.0 | 0.1 | 0.12 | 9 / 1 / 3 |
| preface/TestServerCrashes | 167 | 0.0 | 0.1 | 0.10 | 8 / 0 / 2 |
| probe/deadlinewrite | 467 | 76.4 | 69.4 | 13.37 | 2460 / 10292 / 502 |
| probe/dialthenlisten | 72 | 0.0 | 0.0 | 0.10 | 4 / 0 / 2 |
| probe/dialtimeout | 11372 | 2.0 | 4.4 | 1.12 | 313 / 613 / 75 |
| probe/emptywrite | 94 | 0.0 | 0.1 | 0.11 | 6 / 0 / 1 |
| probe/killwrite | 249 | 46.3 | 46.3 | 7.05 | 1478 / 5199 / 273 |
| probe/resetwrite | 226 | 62.2 | 50.5 | 12.37 | 1762 / 9794 / 597 |
| probe/writeclose | 538 | 92.4 | 80.5 | 15.62 | 2596 / 12281 / 636 |
| probe/writeclosewrite | 538 | 92.4 | 80.5 | 14.92 | 2444 / 11710 / 653 |
| shutdown/TestProcesses | 236 | 0.0 | 0.1 | 0.10 | 11 / 1 / 3 |

**Negative tests** (`certify.py`, on the sample; each must be NOT CERTIFIED at the step, or the
plan or call, it touched, with the expected reason): a Write step's `k` changed (the loop then goes
on: `last` wrong); a Read's `k` not its bytes' count; a Read of one byte of the two the trace read;
a forged EOF (not `ReadOutcome`); a forged EOF the model allows (with a cut keeping nothing) but the
trace did not see (its code); a wrong error kind (an Accept on a closed listener failing sys:
`AcceptStep`; a listener's first Close failing closed: `LisCloseOutcome`); bytes never written,
the trace and the witness agreeing on them (only the model refuses); an unmodeled call; an error net.lean
cannot build (a closed-end error with `Timeout()` true); a plain Dial's deadline error (it maps to
`timeout`, which the witness's `sys` failure is not); an Accept returning another connection; a
call's step missing; a step after its call returned; two steps swapped (`t` order); an ill-formed
plan (an ephemeral port); a crash left out (the restarted node's next step is not of its current
incarnation); a crash before the old process's last record; a Write step of other bytes than the
call's `b[nn:]`. All 19 are rejected where expected.

## The model, transcribed (`model.py`)

| Impl.lean / Deploy.lean | model.py | notes |
|---|---|---|
| `NetStatus`, `NetDir`, `NetDir.fresh`, `NetEnd`, `NetEnd.fresh`, `NetConn` | `OPEN/FIN/CUT`, `NetDir`, `DIR_FRESH`, `NetEnd`, `END_FRESH`, `NetConn` | side False = 0, the dialer |
| `NetConn.fresh`, `NetConn.abandoned` | `conn_fresh`, `conn_abandoned` | |
| `NetConn.endSt`, `.out`, `.setEnd`, `.setOut` | `end_st`, `out`, `set_end`, `set_out` | |
| `NetGlobal`, `NetGlobal.setConn`, `NetLocal` | `NetGlobal`, `.set_conn`, `NetLocal` | dicts, copied on update |
| `endId`, `IsEnd` | `end_id`, `is_end`, `decode_end` | |
| `NetErr`, `NetErr.code`, `errCode` | `CLOSED/TIMEOUT/SYS`, `ERR_CODE`, `err_code` | |
| `ReadRes`, `readRes`'s EOF code | `R_BYTES`, `R_EOF`, `R_ERR`, `EOF_CODE` | |
| `ReadAvail` | `read_avail` | its `∃ k` at k = the bytes' length |
| `ReadOutcome` | `read_outcome` | the cut's `∃ k` given (`keep`) or at its only candidate; tested against every k |
| `WriteOutcome` | `write_outcome` | one step of the Write loop (v3.1) |
| `NetDir.shut`, `CloseOutcome`, `CloseWriteOutcome`, `DeadlineOutcome`, `timeIsZero` | `shut`, `close_outcome`, `close_write_outcome`, `deadline_outcome`, `time_is_zero` | |
| `stripPrefix`, `wildPort`, `portOf`, `ListenAt` | `strip_prefix`, `wild_port`, `port_of`, `listen_at`, `listen_resolve` | `listen_resolve`: the unique a0 (`listenAt_unique`) |
| `ReadStep`, `WriteStep`, `CloseStep`, `CloseWriteStep`, `SetDeadlineStep` | `read_step`, `write_step`, `close_step`, `close_write_step`, `set_deadline_step` | e' as its value |
| `failV`, `NewConn`, `DialStep`, `AcceptStep`, `ListenStep`, `LisCloseOutcome` | `fail_v`, `new_conn`, `dial_step`, `accept_step`, `listen_step`, `lis_close_outcome` | the `∃ c`, `∃ l`, `∃ a0` at their only candidates |
| `NetStep` | `net_step` | not the `Any*` operations (the trusted models' choices, not trace steps) |
| `net_semantics.crash` | `crash` | |
| `isDigit`, `digitsVal`, `decNat`, `splitBy`, `parseAddr`, `addrOk`, `keysDistinct`, `PlanWellFormed` | `is_digit`, `digits_val`, `dec_nat`, `split_by`, `parse_addr`, `addr_ok`, `keys_distinct`, `plan_well_formed` | |
| net.lean: `model.kindErr`, `model.connErr`, `model.opError`, `model.errFlag`, each `*.impl`'s Op, Source, Addr, Syscall | `mapping.py`: `err_kind`, `map_call`, `GO_OP`, `SYSCALL`, `SOURCE_NIL` | read backwards: a Go value to the extension's result |
| net.lean: `model.writeLoop` (`conn.Write.impl`) | `lazy.write`, `replay.py`'s Write steps | count the sum, error the failing step's |

## Tests (`test_check.py`, 77 tests, about 15 s; `go test ./net/conform/check` runs them)

- **The model**: `read_outcome`'s decision of its `∃ k` against trying every k, on every small
  state; Tests.lean's read examples; Write steps; Close; `ListenAt` (wildcards, a shared port);
  Deploy.lean's examples of `PlanWellFormed`; `DialStep` (D16), `AcceptStep`.
- **Lazy against eager**: 3000 random histories of one connection (two ends; Reads, Writes, Closes,
  CloseWrites, deadlines; some calls cut short; random intervals; results from a random execution
  of the model, then some perturbed), half aimed at the corner (Writes, CloseWrites and the peer's
  Reads of one direction). Each is decided by the checker's search over the lazy model and by a brute
  force over every real-time order, every split of every Write into steps and every successor of
  `model.py`'s literal relations; the verdicts must agree (both verdicts are frequent). Run longer
  by hand (seeds 1000 up, histories up to 7 operations): 9000 + 6000 more agree.
- **Positive** hand-made traces, each admitted with a witness that replays: an echo; overlapping
  Writes reordered; a Read before its Write returns; a break (a prefix, a reset, EOF: the witness's
  cuts keep 3 then 0); a Write after the peer's Close (success, EPIPE, success discarded); a partial
  write timing out; a read timeout with data, the deadline cleared; a deadline set while a Read
  blocks; Accepts in another order, a Dial before the Listen (D7); the Write/Close race (D15: steps,
  the Close between); a deadline set while a Write blocks (D15, the axiom review's case: the witness
  has the steps (3, nil) and (0, timeout) of what remained); overlapping Writes interleaved (the
  model allows it); DialTimeout's two timeout shapes accepted (D16); a wildcard Listen (D21); a
  half-close; a killed writer's unfinished Write partly read; a server killed and restarted (its
  crash, the listener reopened); the corner admitted through a retro cut (`cut: {keep: 1}` on the
  peer's Read); a cut by a Write's failure, then CloseWrite, then a Write; calls in progress at
  exit; a reused 4-tuple.
- **Negative** hand-made traces, each NOT ADMITTED at the operation the test names: bytes invented,
  reordered, read twice, read before their Write began, read past what was written; a short
  successful Write; `closed` from a Read of an open end (its Close began after); read and write
  timeouts with no deadline, after it was cleared, and a write deadline set only after the Write;
  a Write failing `closed` with no Close of its end before its end (v3's D15 admitted this; the loop
  does not); data read after the reader's own Close; a Write after the writer's own Close; data
  written after a break read; Close returning sys; a second Close succeeding; SetDeadline of a
  closed end succeeding; the corner with no cut point (a Write, and a partial `closed` one, after
  CloseWrite), and the corner's discarded bytes read; an Accept by a process after its exit event,
  its node restarted; two open listeners at one address; Accept on a closed listener returning sys;
  an Accept no Dial explains, and one whose failed Dial began after it returned; data read from an
  abandoned connection; two Accepts of one failed Dial; a plain Dial failing with a deadline error;
  shapes: a closed error with Timeout true, EOF wrapped, EOF from Write, a bare Errno, a wrong Op, a
  wrong Syscall, bytes with an error, a Read of n > 0 returning nothing, a nil LocalAddr; two time
  namespaces.
- **Scope**: an unmodeled API; an explicit plan without the address; port 0 (out of scope, every
  component admitted, a witness); a hostname Dial; an Accept timeout after an unmodeled listener
  deadline (inconclusive, not a finding).
- **The sample** (`../testdata/*.tar.gz`, 14 runs): all ADMITTED, with witnesses.
- **Mutants of the sample** (`mutate.py`, 3 of each kind per run): all rejected.
- **Certification** (`certify.py`, `certify_test.go`, about 22 s; skipped unless the replay is built
  or `NET_CERTIFY=1`, which builds it): the sample's 14 witnesses CERTIFIED in Lean, and 19
  tampered witnesses (or calls) NOT CERTIFIED where expected ("Certification in Lean").

## Results (2026-11-14, the collection of `../README.md` in `/tmp/net-collect`, 22 runs)

`conform_check.py table /tmp/net-collect/traces`: 21 runs ADMITTED, 1 OUT OF SCOPE, none NOT
ADMITTED; 8.6 s in all (2.2 s of it loading the semantics run's 257 MB). Load and check seconds; the
witness's steps, crashes, Reads that cut (none retro), D16 connections accepted, Write calls of
several steps (every one a race or a deadline), calls cut short in it:

| run | verdict | load s | check s | procs | calls | conns | steps | crashes | cuts | D16 | multi-step Writes | unfinished |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| acceptloop/TestProcesses | ADMITTED | 0.00 | 0.02 | 11 | 162 | 20 | 170 | 9 | 0 | 0 | 0 | 0 |
| acceptloop/TestServerCrashes | ADMITTED | 0.01 | 0.04 | 58 | 780 | 96 | 830 | 56 | 2 | 0 | 0 | 0 |
| duplex/TestProcesses | ADMITTED | 0.00 | 0.01 | 11 | 174 | 10 | 182 | 9 | 10 | 0 | 0 | 0 |
| duplex/TestServerCrashes | ADMITTED | 0.01 | 0.04 | 57 | 787 | 46 | 836 | 55 | 46 | 0 | 0 | 0 |
| echo/TestProcesses | ADMITTED | 0.00 | 0.01 | 21 | 162 | 20 | 179 | 18 | 0 | 0 | 0 | 0 |
| echo/TestServerCrashes | ADMITTED | 0.02 | 0.05 | 117 | 826 | 101 | 934 | 114 | 1 | 0 | 0 | 0 |
| framed/TestProcesses | ADMITTED | 0.01 | 0.02 | 21 | 372 | 20 | 389 | 18 | 10 | 0 | 0 | 0 |
| framed/TestServerCrashes | ADMITTED | 0.03 | 0.11 | 119 | 1818 | 102 | 1928 | 116 | 53 | 0 | 0 | 0 |
| halfclose/TestProcesses | ADMITTED | 0.00 | 0.01 | 11 | 112 | 10 | 120 | 9 | 3 | 0 | 0 | 0 |
| halfclose/TestServerCrashes | ADMITTED | 0.01 | 0.03 | 62 | 582 | 52 | 636 | 60 | 16 | 0 | 0 | 0 |
| preface/TestProcesses | ADMITTED | 0.00 | 0.01 | 21 | 212 | 20 | 229 | 18 | 10 | 0 | 0 | 0 |
| preface/TestServerCrashes | ADMITTED | 0.00 | 0.01 | 26 | 145 | 16 | 167 | 23 | 16 | 0 | 0 | 5 |
| probe/deadlinewrite | ADMITTED | 0.42 | 0.72 | 1 | 460 | 4 | 467 | 0 | 0 | 0 | 7 | 0 |
| probe/dialthenlisten | ADMITTED | 0.00 | 0.00 | 1 | 72 | 8 | 72 | 0 | 4 | 0 | 0 | 0 |
| probe/dialtimeout | ADMITTED | 0.16 | 0.54 | 1 | 11372 | 1891 | 11372 | 0 | 231 | 659 | 0 | 0 |
| probe/emptywrite | ADMITTED | 0.00 | 0.00 | 1 | 118 | 8 | 94 | 0 | 0 | 0 | 0 | 0 |
| probe/killwrite | ADMITTED | 0.11 | 0.38 | 5 | 246 | 4 | 249 | 3 | 4 | 0 | 0 | 4 |
| probe/resetwrite | ADMITTED | 0.27 | 0.33 | 1 | 215 | 6 | 226 | 0 | 0 | 0 | 11 | 0 |
| probe/writeclose | ADMITTED | 0.42 | 0.60 | 1 | 527 | 6 | 538 | 0 | 0 | 0 | 11 | 0 |
| probe/writeclosewrite | ADMITTED | 0.39 | 0.58 | 1 | 527 | 6 | 538 | 0 | 0 | 0 | 11 | 0 |
| semantics/all | OUT OF SCOPE | 2.17 | 0.57 | 11 | 543 | 34 | | | | | | |
| shutdown/TestProcesses | ADMITTED | 0.00 | 0.01 | 20 | 223 | 20 | 236 | 19 | 0 | 0 | 0 | 5 |

(`calls` counts the address queries, which are no steps; `cuts` counts Reads that cut: the
Writes' sys failures cut too.) The semantics run is out of scope for port 0 everywhere (40
listeners, D12), its zero-value sockets (EINVAL), 51 `TCPConn.SyscallConn`, 2 `SetLinger`,
`TCPListener.SetDeadline` (its Accept's timeout: the only inconclusive component), and
TestAddressAliases' `localhost:P` Dials and `:P` wildcard listening at 127.0.0.1:P and 127.0.0.2:P
(no `ListenAt` address); every other component of it is admitted.

**Mutation** (`conform_check.py mutate /tmp/net-collect/traces -n 5`, the 21 admitted runs):
786 of 786 mutants rejected (100%), 87 s: m-flip 94/94, m-short 98/98, m-closeerr 104/104,
m-liscloseerr 16/16, m-readclosed 104/104, m-swap 55/55, m-early 94/94, m-timeout 94/94,
m-closedopen 94/94, m-dialshape 33/33. (The semantics run, OUT OF SCOPE, is not mutated: most of
its components are inconclusive by `SyscallConn`, so its mutants are too; an earlier run that
mutated it rejected 795 of 828, every miss one of its mutants.)

## Findings

- **No real run is NOT ADMITTED.** Every behavior the collection recorded, including the races
  the probe provokes (a Write cut short by Close, by CloseWrite, by a reset, by a deadline, by a
  kill; 659 Accepts of DialTimeouts that failed; crashes and restarts), is an execution of the model,
  with the step-wise Write.
- Under v3's one-step Write (before the change), the same 21 runs were ADMITTED too (the race
  probes then used D15's `closed`-with-a-prefix), and its D15 let a Write at an open end fail
  `closed` with no Close of the end at all; the loop of steps no longer allows that
  (`test_write_closed_with_no_close`).
- Precision notes on the model, each admitted by it and never produced by Go: a Write after the
  end's own CloseWrite succeeding, through a cut at an earlier Read of the peer (the corner; no real
  run needed it); the steps of two overlapping Writes of one end interleaving (Go's `fdMutex`
  serializes them; no real run needed it); an Accept returning a connection whose 4-tuple is not
  its own (D18's arbitrary addresses; the checker does not search those).
- Scope: the measured semantics tests are out of scope as a whole (port 0, unmodeled APIs); the
  examples and the probe use none of what the model lacks.

## Limitations

- Not proved: `model.py` is transcribed by hand, the lazy model's exactness is argued above and
  tested against a brute force on small histories. An ADMITTED verdict is certified in Lean
  ("Certification in Lean"); a NOT ADMITTED one is not (the search's completeness, and so a
  refutation, rests on the exactness argument and `model.py`).
- The pairing of ends by 4-tuple (above); an unpaired Accept is explained by any failed or
  unfinished Dial of its address, not by its host.
- Splits of overlapping Writes of one end are tried only up to 64 bytes left (a failure past that
  is inconclusive).
- The tracer sees `net`'s API: each call's effect is taken to be within its traced interval.
- Crashes are placed by the drivers' events; with none (the semantics run), processes of one name
  that overlap are separate nodes.
