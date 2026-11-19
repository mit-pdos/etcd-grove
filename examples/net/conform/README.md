# conform: traces of real runs, for checking them against the TCP semantics

The net extension's semantics (`GooseLang/Ext/Net/Impl.lean`) is trusted: every theorem over the
examples holds for the behaviors it allows, and `examples/net/semantics/` backs each decision with
one measured test. This directory records whole runs of real programs, every call of Go's `net`
they make, so that a conformance checker can decide whether some execution of the semantics
produces each run (`notes/net-tcp-v3-plan.md`, E10; dsverify-lab's `harness/conform`,
`notes/net-tcp-dsverify-survey.md` §2). This is the tracing half: the tracer, the trace format,
the probe, the collection. The checker (the transcription of `Impl.lean` and the linearizability
search) comes after the semantics v3; "What the checker needs" says what it will read.

| file | what |
|---|---|
| `overlay/zz_netext_trace.go.src` | the tracer: a file added to Go's own `net` package at build time |
| `overlay/zz_netext_goid.go.src` | a file added to Go's `runtime`: the goroutine's id, for the tracer |
| `overlay/overlay.go` | writes the `go build -overlay` file (`overlay.Make`); `cmd/overlay` is its command |
| `events/events.go` | a driver's file of process events (start, kill, exit), written by `proctest` and the probe |
| `probe/main.go` | the probe: one mode per pattern that stresses the semantics |
| `tracecheck/tracecheck.go` | loads trace directories and checks they are well formed (not against the model); `cmd/tracecheck` is its command |
| `collect_test.go` | `TestCollect` (the collection, with `NET_CONFORM=1`), `TestSample` (the sample is well formed), `TestOverlay` (the renames match the installed Go) |
| `testdata/*.tar.gz` | the sample: 14 trace directories (452 KB), the checker's test inputs |
| `../internal/proctest/conform.go` | `proctest`'s tracing, with `NET_CONFORM=1` |

## Collecting traces

```
cd examples
NET_CONFORM=1 NET_CONFORM_OUT=/tmp/net-conform go test -count=1 -timeout 60m -v -run TestCollect ./net/conform
go run ./net/conform/cmd/tracecheck /tmp/net-conform/traces      # check again, print the counts
```

`TestCollect` writes the overlay (`overlay/`), runs the seven examples' `TestProcesses` and
`TestServerCrashes` (`go test -p=1`, each command built with the overlay by `proctest`), builds the
probe with the overlay and runs each of its modes, then checks every trace directory with
`tracecheck` and writes the counts to `summary.txt`. Options:

- `NET_CONFORM_OUT=DIR`: where everything goes (must be empty or absent); else a fresh temporary
  directory, logged.
- `NET_CONFORM_SEMANTICS=1`: also `go test -overlay` the measured semantics tests
  (`traces/semantics/all`, one directory: the tests run in parallel in one process; their child
  processes are killed by the tests, which record no events, so this directory is checked
  leniently). A failing semantics test is logged, not fatal (see "Limitations").
- `NET_CONFORM_SAMPLE=1`: also rewrites `testdata/`: six of the examples' directories, and each
  probe mode run once more with one iteration (`dialtimeout` with 300 dials).

Run `TestCollect` alone: `NET_CONFORM=1 go test ./net/...` would run the examples' own process
tests in parallel with the collection's runs of them, on the same ports.

The layout of `DIR`:

```
overlay/overlay.json, overlay/net/*.go, overlay/runtime/*.go
bin/probe
traces/<example>/<Test>/         one directory per run of a process test (proctest)
traces/probe/<mode>/             one per probe mode; traces/probe/<mode>.txt is the probe's report
traces/semantics/all/            with NET_CONFORM_SEMANTICS=1
examples.txt, semantics.txt      the go test outputs
summary.txt                      tracecheck's counts
sample/                          with NET_CONFORM_SAMPLE=1
```

A trace directory is one run of one system: every process of it, each in its own file, and the
driver files of the processes that started them. The checker checks a directory as a whole.

**By hand.** `go run ./net/conform/cmd/overlay DIR` prints the overlay file's path; build with
`go build -overlay PATH ...` (or `go test -overlay PATH ...`) and run with `NET_TRACE_DIR` (and
`NET_NODE`) set. `proctest` does exactly this with `NET_CONFORM=1`: `Build` builds with the
overlay (`$NET_OVERLAY` if set, else one it makes), `Start` and `Run` set `NET_NODE` to the
command's name and `NET_TRACE_DIR` to `$NET_TRACE_DIR/<package>/<test>` (a fresh one per
test run; a temporary root if unset), and write the directory's driver file. Without
`NET_CONFORM=1` nothing changes: the same `go build` command, the same process environment.

## The tracer

**How.** `go build -overlay` replaces four files of Go's own `net` package and adds one to `net`
and one to `runtime`. In the replaced files (`net.go`, `dial.go`, `tcpsock.go`,
`tcpsock_unix.go`) the only change is that each traced definition is renamed `netextOrig<Name>`,
plus one call inside `net` (`newTCPConn`'s `SetKeepAliveConfig`, which Go makes on its own, now
calls the original: the trace holds only the program's calls). The added `zz_netext_trace.go`
defines `<Name>` as a wrapper: it builds the begin record, takes the time, writes the record,
calls the original, takes the time, writes the end record. `overlay.Make` fails unless each of
the 38 renames and the call patch matches exactly one line, unless the four bodies the wrappers
re-implement are exactly Go's (`Dial`, `DialTimeout` and `Dialer.Dial` are a call of
`Dialer.DialContext`, `Listen` one of `ListenConfig.Listen`; the wrappers call the originals of
those directly, so that one program call is one record), and unless `go env GOVERSION` is
`go1.27.3` (the target configuration, D13). `TestOverlay` runs `overlay.Make` on every `go test`.
The toolchain on disk is not modified, and neither are the programs.

**Off.** A binary built without the overlay is unchanged: the commands import nothing of this
directory, and `proctest` builds with the same command line (checked: `echo/cmd/server`,
`halfclose/cmd/client` and `shutdown/cmd/node` built from the commit before this directory and
after it, `-trimpath -buildvcs=false`, have the same sha256). A traced binary run without
`NET_TRACE_DIR` (or with it empty) calls the originals at once and writes nothing. With it
set, a traced process that cannot create its trace file exits 97 at `net`'s initialization: a
run that silently lost a process's trace would be checked as if the process had made no call.

**Traced, in the model** (an op of its own; `Net/Code/net.toml`'s trusted functions, and the
v3 plan's `DialTimeout`, addresses): `Dial`, `DialTimeout`, `Listen`; `(*TCPListener).Accept`
(also `Listener.Accept` on a `*TCPListener`, the same method), `Close` (op `ListenerClose`),
`Addr` (op `ListenerAddr`); `(*conn)` `Read`, `Write`, `Close`, `SetDeadline`, `SetReadDeadline`,
`SetWriteDeadline` (one op, `SetDeadline`), `LocalAddr`, `RemoteAddr` (promoted to `*TCPConn`
and the other conns); `(*TCPConn).CloseWrite`.

**Traced, out of scope** (op `Unmodeled`, field `api`; the model has no step for them):
`Dialer.Dial`, `Dialer.DialContext`, `Dialer.DialTCP`, `DialTCP`, `ListenConfig.Listen`,
`ListenTCP`, `TCPListener.AcceptTCP` (each recorded with its dial, listen or accept arguments and
the socket it returns, so that the socket's later operations have an id), `conn.SetReadBuffer`,
`conn.SetWriteBuffer`, `conn.File`, `TCPConn.SyscallConn`, `ReadFrom`, `WriteTo`, `CloseRead`,
`SetLinger`, `SetKeepAlive`, `SetKeepAlivePeriod`, `SetKeepAliveConfig`, `SetNoDelay`,
`MultipathTCP`, `TCPListener.SyscallConn`, `SetDeadline`, `File`.

**Not traced:** `net`'s other APIs (UDP, Unix, IP sockets' own functions, `ListenPacket`,
`FileConn`, `FileListener`, `net.Pipe`, name resolution). A socket made by one of them is named
`u<k>` when a traced method is first called on it (a `*UDPConn`'s `Read` is `(*conn).Read`).
Calls Go makes inside `net` of a traced method on a socket the program never saw: only
`dialParallel`'s `Close` of the losing connection, with a dual-stack fallback (a host name with
IPv4 and IPv6 addresses; never with the examples' IP literals), recorded as a `Close` of a `u`
socket. `TCPConn.ReadFrom` and `WriteTo` without `splice`/`sendfile` call the traced `Write` or
`Read`, recorded inside the `Unmodeled` call. A socket closed by Go's finalizer (a leaked one)
or by the kernel at a process's exit leaves no record.

## The trace format

Version 1. The tracer (`zz_netext_trace.go.src`, `netextVersion`), `events` (`Version`) and
`tracecheck` (`Version`) implement it; change them, and this section, together.

**Files.** One file per process, in the directory `NET_TRACE_DIR` names: a node's
`<node>.<pid>.<t>.jsonl` (`<node>` is `NET_NODE`, default the executable's base name, with
bytes outside `[A-Za-z0-9._-]` replaced by `_`; `<t>` the monotonic time at the file's creation),
a driver's `_driver.<pid>.<t>.jsonl`. Each line is one JSON object, a record, written by one
`write(2)` on a file opened `O_APPEND` (records of one file are in the order they were written,
and no returned call's record is lost when the process is killed; a record being written when
the process was killed may be cut short: the file's last line, then not JSON or with no final
newline). Member order within a record is not significant. Integers are JSON numbers (exact
below 2^53: times, counts, pids).

**Clock.** `t`, `t0`, `t1` are `CLOCK_MONOTONIC` in nanoseconds (`runtime.nanotime` in a node,
`clock_gettime` in a driver), one clock for every process in one time namespace (the header's
`timens`).

### The header: `"k": "H"`, the first line of every file

| field | value |
|---|---|
| `v` | 1, the format version |
| `role` | `"node"` (a traced process) or `"driver"` (a process that started nodes) |
| `pid`, `ppid` | the process's and its parent's pid |
| `node` | the node's name (`NET_NODE`); a driver's own name (`"proctest"`, the probe's node) |
| `exe`, `args` | `os.Executable()`, `os.Args` |
| `go` | `runtime.Version()` |
| `host` | `os.Hostname()` |
| `timens`, `netns` | `readlink /proc/self/ns/time`, `.../ns/net` (`"time:[4026531834]"`) |
| `file` | the file's path |
| `t0`, `wall`, `t1` | monotonic time, then `time.Now().UnixNano()`, then monotonic time: `wall` was read between `t0` and `t1` |

### A node's records: `"k": "B"` (a call began) and `"k": "E"` (it returned)

Every call of a traced function or method writes one `B` record and, when it returns, one `E`
record. Fields of both:

| field | value |
|---|---|
| `pid`, `node` | the process's, as in the header |
| `s` | the call's number in this process, from 1, the same in its `B` and `E` (unique per process; not in file order: concurrent calls take numbers before writing) |
| `g` | the calling goroutine's id (the same in `B` and `E`) |
| `op` | the operation (the table below) |
| `id` | the socket operated on, for the operations on a socket (below); the same in `B` and `E` |
| `t` | `B`: the time just before the original was called (after the record was built, before it was written); `E`: the time just after it returned. The interval `[B.t, E.t]` contains the call of Go's own function |

A `B` record is written before its `E` record, and an `E` record before the wrapper returns: a
call that uses a socket another call returned begins after that call's `E` record. A `B` record
with no `E` record is a call that had not returned when its process ended (killed, or exited
with the call in progress in another goroutine).

**Socket ids** (`id`, and `new.id` below): `"c<k>"` a connection a dial or an accept returned,
`"l<k>"` a listener a listen returned, `"u<k>"` a socket first seen by an operation on it (made by
an API that is not traced), `"nil"` no socket (a nil `*TCPConn`, a zero-value `TCPConn` or
`TCPListener`: the call fails with `EINVAL`, or panics). `<k>` counts from 1 in each process, one
counter for all three prefixes. An id is never reused within a process: the tracer keys its map
by weak pointers to the `netFD`, so a new socket at a reclaimed one's address gets a new id (and
tracing keeps no socket alive). A socket's global name is (`pid`, `id`).

**Operations.** Arguments are in `B`, results in `E`; every `E` but the address queries' has `err`.

| `op` | `id` | `B` arguments | `E` results |
|---|---|---|---|
| `Dial` | none | `net`, `addr` (the strings passed) | `new` (on success), `err` |
| `DialTimeout` | none | `net`, `addr`, `timeout` (ns) | `new` (on success), `err` |
| `Listen` | none | `net`, `addr` | `new` (on success, an `l` id, `remote` null), `err` |
| `Accept` | the listener | | `new` (on success), `err` |
| `ListenerClose` | the listener | | `err` |
| `ListenerAddr` | the listener | | `addr` |
| `Read` | the connection | `n`: the buffer's length | `n`: the count; `data`: the bytes read, hex (present iff `0 < n`); `err` |
| `Write` | the connection | `n`: the length; `data`: all the bytes, hex | `n`: the count; `err` |
| `Close` | the connection | | `err` |
| `CloseWrite` | the connection | | `err` |
| `SetDeadline` | the connection | `which`: `"both"` (`SetDeadline`), `"read"`, `"write"`; `set`: `!t.IsZero()` (false: the deadline is cleared); when set, `in`: `time.Until(t)` at the call (ns, negative if past), `wall`: `t.UnixNano()` | `err` |
| `LocalAddr`, `RemoteAddr` | the connection | | `addr` |
| `Unmodeled` | the socket, if a method | `api` (`"TCPConn.SetNoDelay"`, `"Dialer.DialContext"`, ...); a dial: `net`, `addr` (`DialTCP`'s: `raddr.String()`), `timeout` if the `Dialer`'s is set, `laddr` (an address) if set, `ctxDeadlineIn` (ns) if the context has a deadline; a listen: `net`, `addr` | `api`; a dial, listen or accept: `new` (on success); `err` |

`new`, the socket a call returned: `{"id", "net", "local", "remote"}`: its id, its `fd.net`
(`"tcp"`, `"tcp4"`, ...), and its local and remote addresses (Go's `fd.laddr` and `fd.raddr`,
which `LocalAddr` and `RemoteAddr` return), each an address object. `null` if the call succeeded
with no socket the tracer knows (never seen).

**An address**: `null` for a nil interface; `{"type": T, "nil": true}` for a nil pointer of a
known address type; else `{"type": T, "net": a.Network(), "s": a.String()}`, `T` the dynamic
type (`"*net.TCPAddr"`). A TCP address's `s` is `IP:port` (`[IPv6]:port`).

**An error**, `err`: `null` for nil; else an object:

| field | value |
|---|---|
| `type` | the dynamic type (`"*net.OpError"`, `"*errors.errorString"` for `io.EOF`, `"syscall.Errno"`) |
| `msg` | `Error()` |
| `eof` | `err == io.EOF` |
| `isEOF`, `isClosed`, `isDeadline` | `errors.Is(err, io.EOF)`, `errors.Is(err, net.ErrClosed)`, `errors.Is(err, os.ErrDeadlineExceeded)` |
| `timeout`, `temporary` | `Timeout()`, `Temporary()`, present iff the error has the method |
| `op`, `net`, `source`, `addr`, `inner` | present iff the error is a non-nil `*net.OpError`: its `Op`, `Net`, `Source` and `Addr` (address objects), and its `Err`'s dynamic type (`"*os.SyscallError"`, `"poll.errNetClosing"`, `"*poll.DeadlineExceededError"`, `"*net.timeoutError"`, `"nil"`) |
| `syscall` | present iff the error, or the `*OpError`'s `Err`, is an `*os.SyscallError`: its `Syscall` (`"write"`, `"connect"`) |
| `errno` | the `syscall.Errno`'s number, present iff that `*os.SyscallError`'s `Err` is a `syscall.Errno`, or the error (or the `*OpError`'s `Err`) is itself one (then with no `syscall`) |

### A driver's records: `"k": "P"`, process events

A driver (`proctest`; the probe's `killwrite`) records each node process it starts, kills and
waits for. Fields: `pid`, `node` (the driver's), `s` (the event's number in the file, from 1),
`ev`, `t`, `cnode` (the node's name, its `NET_NODE`), `cpid` (its pid), and by event:

| `ev` | meaning | more fields |
|---|---|---|
| `start` | the process was started (`t` after `Start` returned: its own records come later) | `bin`: the executable |
| `kill` | SIGKILL is about to be sent (`t` before the signal; the process ends between this event and its `exit`) | |
| `exit` | the process has ended (`t` after `Wait` returned: no record of it comes later) | `code`: its exit code, -1 if it was ended by a signal; `signal` (`"killed"`), `signo`: present iff it was |

Every process a driver starts gets an `exit` event. A `kill` only for a process the driver saw
still running; a process can be ended by SIGKILL with no `kill` event (`proctest.Run`'s timeout,
`exec.CommandContext`): the `exit` event's `signal` says it.

## What the checker needs from the traces

- **The two ends of a connection** are paired by 4-tuple: a dial's `new.local.s`/`new.remote.s`
  are an accept's `new.remote.s`/`new.local.s`, swapped, in the same directory (all processes run
  on 127.0.0.1). Ephemeral ports can be reused within a run (a 4-tuple can name several
  connections in turn: the latest dial called before the accept returned, as dsverify-lab's
  checker pairs them). An accepted connection that no dial returned comes from a dial that failed
  after the handshake (an abandoned dial, v3's E3: frequent in `probe/dialtimeout`, see below) or
  from a dial whose process ended inside the call; a failed dial has no local address, so it is
  matched by address and time only.
- **Crash events between a node's processes**: a node is its `node` name in the directory, its
  processes the files with that name, in time order. A process ends after its last record and
  before its driver's `exit` event (after `kill`, if any); a later process of the same node is
  the node after a crash (the model's crash relation: its listeners gone, its connections kept).
  The killed processes' calls with no `E` record never returned; a `Write` among them may have
  sent any prefix of its bytes (`probe/killwrite`: the reader read 536,683 bytes of the 1 MiB
  `Write` that never returned, then EOF). A process that exits (code 0 or a panic's 2) is the
  same event for its peers (D11). Processes in the semantics directory have no driver events.
- **Causal order**: one clock. Check that every header in a directory has the same `timens`,
  that the `wall - (t0+t1)/2` offsets agree across processes, that an accept returns after its
  dial began, and that every operation on a socket begins after the `E` of the call that returned
  it (guaranteed within a process). Real-time order across processes: `a` precedes `b` iff
  `a`'s `E.t` < `b`'s `B.t`; within a goroutine (`pid`, `g`) the calls are sequential.
- **The plan**: the addresses (`Listen`'s `addr`, and the examples' constants) and which node
  listens at each; the examples use fixed ports 7101-7107 and the probe 7191-7198, outside the
  ephemeral range; the semantics tests use port 0 (out of the model's scope, D13).
- **Scope**: `Unmodeled` calls, ops on `u` and `nil` sockets, networks other than `"tcp"` have no
  step in the model.

## The probe (`probe/`)

The examples' messages are a few bytes, so their `Write`s never block midway. The probe drives,
over 127.0.0.1, the patterns where a Go call is not one atomic kernel operation, each a mode
(`probe -mode M [-iters N] [-size BYTES] [-addr A]`), listening at 127.0.0.1:7191-7198. The race
modes first fill the connection's buffers (256 KiB `Write`s under a 20 ms write deadline until one
times out, the reader not reading), so the 1 MiB `Write` that follows blocks at once; the reader
then reads slowly (64 KiB, then a 1-2 ms pause). Every stream is a pattern of period 251, so a
reader checks each byte it reads against the writer's at that offset (and the probe's report
notes any mismatch).

| mode | pattern |
|---|---|
| `writeclose` | a 1 MiB `Write` while another goroutine `Close`s the writer's end 2-31 ms later |
| `writeclosewrite` | the same with `CloseWrite` |
| `resetwrite` | a 1 MiB `Write` while the reader reads for 2-21 ms and then `Close`s with unread input (a reset); then a `Write` and two `Read`s on the reset end |
| `killwrite` | a child process (the probe re-executed, node `<node>.writer`) dials and writes 1 MiB `Write`s; the parent reads 256 KiB slowly, kills the child (SIGKILL, with `kill`/`exit` events in its own driver file) while it is blocked in a `Write`, and reads on to EOF |
| `deadlinewrite` | a 1 MiB `Write` past a 10-19 ms write deadline (`k < len`, timeout), the deadline cleared, the rest written; a `Read` past a 3 ms read deadline; `SetDeadline` cleared; `CloseWrite`; the reader checks it read the whole stream |
| `emptywrite` | empty `Write`s on a live end (both ends), past an expired deadline, after `CloseWrite`, after `Close`, after a reset (twice); empty `Read`s; `LocalAddr`, `RemoteAddr`, the listener's `Addr` |
| `dialthenlisten` | `Dial` and `DialTimeout` with no listener; `Listen`; a second `Listen` of the address; `Dial`, `Accept`, a byte, `Close`, EOF; a `Dial` never accepted, the listener's `Close`, a `Read` of that connection; `Accept` and `Close` after `Close`; `Dial` after it |
| `dialtimeout` | 2000 `DialTimeout`s with timeouts of 1-300 µs, each success writing a byte and closing; the listener accepts every connection and reads it to its end |
| `concwrite` | two goroutines `Write` 1 MiB each of distinct bytes to one end at once, the reader slow (64 KiB, 1 ms pauses); the reader checks each `Write`'s bytes are contiguous (v3.3, D25: Go's write lock); its sample (`testdata/probe-concwrite.tar.gz`, 256 KiB each) written by `TestSampleMode` (`NET_CONFORM_SAMPLE_MODE=concwrite`) |

The probe always exits 0 (1 if its own `Listen` fails): the checker judges the run.

## What the traces show (a collection run, 2026-11-14)

`TestCollect` with `NET_CONFORM_SEMANTICS=1`, 55 s: 22 trace directories (14 process-test
runs, 8 probe modes, the semantics tests), 578 node processes and 14 driver files, 42,569
records, 20,378 calls; 46 processes killed (SIGKILL), 46 calls cut short by a kill, 11 in
progress at an exit (shutdown's node exits with goroutines blocked in `Accept`, `Read`,
`Close`), no line cut short. Every directory is well formed. Calls: 6,650 `Read`, 4,348 `Close`,
3,380 `Write`, 2,518 `Accept`, 2,004 `DialTimeout`, 663 `Dial`, 413 `SetDeadline`, 120 `Listen`,
86 `CloseWrite`, 74 `ListenerClose`; out of scope only in the semantics tests (51
`TCPConn.SyscallConn`, 2 `SetLinger`, 1 `TCPListener.SetDeadline`). What stands out:

- **`Write` returns `k > 0` with `net.ErrClosed`** (`writeclose`, 5 of 6 iterations, the 6th
  `(0, ErrClosed)`; the reader read exactly the `k` bytes in each, then EOF): v3's E2. Likewise
  `k > 0` with `EPIPE` after the writer's own `CloseWrite` (`writeclosewrite`, 5 of 6, the reader
  reading exactly `k`), with `ECONNRESET` (`resetwrite`, 5 of 6; the next `Write` `EPIPE`, the
  writer's `Read`s then EOF, not the reset), and with a timeout (25: `deadlinewrite`'s and the
  fills' last `Write`s).
- **Accepts of connections whose `DialTimeout` failed** (`dialtimeout`): of 2000 `DialTimeout`s
  (1-300 µs), 1232 succeeded and 768 timed out; the listener accepted 1891 connections, 659 of
  them returned by no `Dial` (86% of the timeouts), and every one of those read EOF first: v3's
  E3.
- **Two shapes of a `DialTimeout` timeout**: 413 are an `*OpError` wrapping
  `*poll.DeadlineExceededError` (`errors.Is(err, os.ErrDeadlineExceeded)` true: the deadline fired
  in `connect`'s wait for writability), 355 one wrapping `net`'s `*timeoutError` (`Is` false:
  the context's deadline fired first, `mapErr`); both have `Timeout()` true. v3's E1 names only
  `errTimeout` for a `DialTimeout` timeout.
- **A killed writer's unreturned `Write`** delivered part of its bytes (`killwrite`, 4 of 4:
  2,097,152 bytes returned by the child's `Write`s, 2,633,835 read, then EOF).
- **Bare `syscall.Errno` errors** (not `*OpError`): `EINVAL` from the semantics tests' calls on
  zero-value conns and listeners (`id` `"nil"`).
- **Empty `Write`s fail**: `(0, ECONNRESET)` then `(0, EPIPE)` after a reset, `(0, EPIPE)` after
  `CloseWrite`, a timeout past the deadline, `ErrClosed` after `Close`; `(0, nil)` on a live end.
- No `Read` returned bytes and an error at once; every `io.EOF` is unwrapped.

## Differences from dsverify-lab's tracer

dsverify-lab's `harness/conform` (`trace/zz_conform_trace.go.src`, `overlay.py`, `probe/`) is the
model; the approach (renamed definitions in Go's own files, wrappers with the public names, one
`write(2)` per JSON record, `runtime.nanotime`) is the same. What differs:

- **The ops follow our model**: `CloseWrite` is an op (our `CloseWriteStep`; theirs out of scope),
  `DialTimeout` an op of its own (v3's E6), and `Dialer.Dial`, `Dialer.DialContext`,
  `ListenConfig.Listen`, `DialTCP`, `ListenTCP`, `AcceptTCP` are `Unmodeled` (their checker reads
  them as their in-model counterparts; ours has no step for them).
- **Processes are nodes, and they crash**: every record carries `pid` and `node` (from
  `NET_NODE`, not the rig's `DSRIG_ID`); drivers record each process's start, kill and exit
  (their rig did not restart nodes); the probe kills a writer mid-`Write`.
- **The goroutine** is recorded (`g`), through a two-line file added to `runtime` by the same
  overlay; theirs records none.
- **Socket ids by weak pointers**: their map holds every `netFD`, which keeps leaked sockets
  alive and disables Go's finalizer close; ours keeps none alive and still never reuses an id.
- **Errors in full**: the dynamic types (of the error, and of an `*OpError`'s `Err`), the
  `*OpError`'s `Source` and `Addr`, `syscall`, the errno through the `*os.SyscallError` path (or a
  bare `Errno`), `errors.Is` for EOF, `ErrClosed` and `ErrDeadlineExceeded` separately; theirs a
  class string (`"closed"`, `"deadline"`, ...), `Op`, `Net`, `Timeout`, `Temporary`, `errors.As`'s
  errno, `Error()`.
- **Addresses** are objects (type, network, string), a nil interface distinguished from a nil
  pointer; **strings** keep valid UTF-8 (theirs escapes each non-ASCII byte as a separate
  `\u00XX`, which misreads UTF-8).
- **Deadlines** record `in` and `wall`, and nil receivers are traced (`id` `"nil"`; theirs calls
  the original untraced).
- **Stricter generation**: the overlay also checks the bodies the wrappers re-implement, refuses
  a Go other than 1.27.3 (theirs warns), is Go (embedded, used by `proctest` directly) rather
  than Python, and a process that cannot open its trace file exits instead of running untraced.
- **Times**: one per record, `B.t` taken after the record is built (just before the call, so the
  hex encoding of a `Write`'s bytes is outside the interval); theirs `t` in `B` and `t0`/`t1` in
  `E`.
- **The probe** fills the buffers before its races (on loopback a 1 MiB `Write` otherwise goes
  into the socket buffers at once) and adds `writeclosewrite`, `killwrite`, `deadlinewrite`,
  `emptywrite` and `dialthenlisten`; it needs no network emulation (theirs used the rig's netem
  delay and resets).

## Limitations

- **The tracer is not free.** A call's records are built and written before and after the
  original; a `Write`'s bytes are hex-encoded before it. A program's timing changes: a deadline
  set before a large `Write` partly passes while the tracer encodes it. `semantics`'
  `TestWriteDeadlinePrefix` (a 64 MiB `Write` under a deadline) fails when traced (`n = 0`: the
  deadline passed before `write(2)` ran) and passes untraced; the probe's deadlines are sized
  for it (20 ms per 256 KiB).
- **Traces are large**: every `Write`'s and every `Read`'s bytes, in hex (the collection above:
  575 MB, mostly the probe's race modes; the sample, gzipped, 452 KB).
- **The tracer sees `net`'s API, not the kernel**: an operation's effect is taken to be within its
  interval, which holds because the wrapper's interval contains the original's.
- **Failed dials have no local address** (see pairing above).
- **Semantics tests**: one process for all the tests (in parallel), kernel-chosen ports, children
  killed with no driver events; useful as positive traces for single decisions, checked
  leniently.
