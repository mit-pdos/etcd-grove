# Sticky read errors in the net extension's semantics

Status (2026-11-24): **the semantics change and its laws are implemented** (2026-11-23, branch
`net-sticky-read`, approved by the user on etcd-grove#24, option (A)), and **`rerr` is removed**
(branch `net-rpc-rerr`, part 2, option (B): "Part 2 implemented", at the end). Below, the plan as it
was signed off, then what was implemented and how it differs.

Plan (2026-11-23): The decision (the user's, on etcd-grove#24,
2026-11-23): "fix it once in the net extension's semantics, not with per-call-site wrappers,
provided Linux gives no bytes after a read error". This note has the evidence that Linux gives
none (but after a read deadline's timeout), the exact rule, the Lean changes, and what happens to
the three wrappers. Nothing in `GooseLang/Ext/Net/` has changed yet; the tests are in
`examples/net/semantics/sticky_test.go` and `sticky_netns_test.go` (indexed in its `doc.go`,
"Sticky read errors").

## Today

`ReadOutcome` (`GooseLang/Ext/Net/Impl.lean`, D1) lets a `Read` return a `sys` error from any
cut direction, whatever is still unread (`ReadAvail`'s third clause: `d.status = .cut ∧ r = .err
.sys ∧ d' = d`), and a read may cut the direction keeping a prefix of its bytes and answer `sys` at
once (the break clause). Either way the unread bytes stay, and a later `Read` returns them. So the
model allows: `ECONNRESET`, then bytes. Linux never does (below), and the Go code above `Read`
relies on that: `textproto`'s `ReadLine` returns a line cut by an error without the error, `bufio`
keeps no error, gob reads on after an error. So three model wrappers re-impose Linux's behaviour
above `Read`:

| wrapper | where | what it does |
|---|---|---|
| `serverCodec.rerr` | `models/net/rpc/codec.go` (on `lean`); specs `Net/Spec/net/rpc/serverCodec__ReadRequest{Header,Body}.lean`, `newServerCodec.lean`; `rdrOwn`, `rdErr` (`Net/Proof/net/rpc/ServerDefs.lean`) | the first frame read error is kept, and every later frame read returns it without reading |
| `connectReader` | `models/net/rpc/client.go` (branch `origin/models-rpc-http`); `crSt`, `crErr`, `crErr_final` (`Net/Proof/net/rpc/HttpDefs.lean`), `connectReader.Read.spec` | `DialHTTPPath`'s reader of the `CONNECT` answer: after an error, reads into a buffer of its own and returns no byte |
| `connReader.failed` | `models/net/http/server.go` (branch `origin/models-rpc-http`); `Net/Proof/net/http/{ConnReader,ConnReaderHead,connReader__Read}.lean` | the server's connection reader: after an error (but `abortPendingRead`'s timeout), no byte |

Each is "MODEL:" code that Go does not have, and each states a claim narrower than Go's: rpc's
and http's say the model's behaviour is Go's "but for a read deadline's timeout".

EOF and `closed` are already sticky in the model: EOF needs a direction with nothing unread and not
open (`ReadAvail`'s second clause), and no outcome adds bytes to such a direction (`WriteOutcome`
appends only into an open one; a read's cut keeps a prefix of nothing); `closed` needs
`NetEnd.closed`, which nothing clears. Only `sys` is not.

## Evidence (configuration C: Linux 7.0.0-38-generic, Go 1.27.3, 2026-11-23)

Every test reads on past the first error and records the unread count (`SIOCINQ`) when the error
came. Counts: `go test -run Sticky -count=100` (loopback tests, 100/100 each, in parallel) and
`NET_NETNS=1 go test -run TestStickyTimedOut -count=20` (20/20, as root by `sudo -n`).

| test | what it does | measured | passed |
|---|---|---|---|
| `TestStickyEOF` | peer writes `xyz`, `CloseWrite`; then (after the reader's EOF) the peer `Close`s with the reader's bytes unread, a RST | `xyz`, EOF ×5; after the RST still EOF ×4 (`SOCK_DONE` is tested before `sk_err`), never `ECONNRESET`; the reader's `Write` after its EOF `(4, nil)` (its direction is open), after the RST `(0, EPIPE)` | 100/100 |
| `TestStickyReset` | `hello` received, unread; the peer resets (`Close` with unread input) | `hello`, `ECONNRESET` with 0 unread, EOF ×4; a `Read` with an expired deadline: `timeout`, no byte; an empty `Read`: `(0, nil)`; `Write` `(0, EPIPE)` ×2 | 100/100 |
| `TestStickyResetBlockedRead` | a `Read` waits, nothing unread; the peer resets (`SetLinger(0)`, `Close`) | `ECONNRESET`, 0 unread, EOF ×3 | 100/100 |
| `TestStickyKilledPeer` | a child process writes `hello` and is killed (SIGKILL), or exits, with the parent's byte unread | `hello`, `ECONNRESET` with 0 unread, EOF ×4; `Write` `(0, EPIPE)` | 100/100 (both roles) |
| `TestStickyOwnClose` | the reader `Close`s its end with `abc` unread | `Read` `(0, ErrClosed)` ×3, never the bytes; `Write` `(0, ErrClosed)` | 100/100 |
| `TestStickyNotTimeout` | a `Read` times out (20 ms deadline); the peer writes `abc`; the deadline stays expired, then is cleared | `timeout`; `timeout` with 3 unread; the reader's `Write` `(2, nil)`; cleared: `abc`, then the peer's next `de` | 100/100 |
| `TestStickyTimedOut` (netns), partition | `s2c-unread` received, unread; `TCP_USER_TIMEOUT` 2 s, 14 bytes unacknowledged; the router drops everything; read once the socket is `CLOSE` | `s2c-unread`, `ETIMEDOUT` (sys) with 0 unread, EOF ×3; `Write` `(0, EPIPE)` ×2 | 20/20 |
| `TestStickyTimedOut` (netns), ICMP | the same, the router answering the client's packets with ICMP host-unreachable | `s2c-unread`, `EHOSTUNREACH` (sys: the soft error the timeout reports, `tcp_write_err`'s `sk_err_soft ?: ETIMEDOUT`) with 0 unread, EOF ×3; `Write` `(0, EPIPE)` ×2 | 20/20 |

Also already measured, consistent with the rule: `TestResetCloseUnreadInput`, `TestResetLingerZero`,
`TestKilledWithUnreadInput` (bytes, `ECONNRESET`, EOF), `TestResetInNetwork` (a middlebox's RST:
bytes, `ECONNRESET`, EOF), `TestTimeoutOnBreak` (`ETIMEDOUT`, then EOF, EOF),
`TestResetErrorTakenByWrite`/`TestKilledResetTakenByWrite` (the error taken by a `Write`: the
reads are the bytes then EOF, with no read error: outside the rule, which is about read errors).

**The error kinds a `Read` can return** (D14) and what the tests found:

| kind | Linux/Go source | sticky? |
|---|---|---|
| EOF (`ReadRes.eof`) | FIN (`tcp_fin`: `RCV_SHUTDOWN`, `SOCK_DONE`), or after a reset's error was taken | yes (`TestStickyEOF`, `TestReadEOFAfterFin`); the model already |
| `closed` | own `Close` (`poll.FD` refuses once closing) | yes (`TestStickyOwnClose`); the model already |
| `sys` | `ECONNRESET` (a RST: peer's close with unread input, linger 0, killed peer, middlebox); `ETIMEDOUT` (user timeout, keepalive, retransmissions); `EHOSTUNREACH` (the soft ICMP error a timeout reports); in Linux's `tcp_recvmsg_locked` only when nothing was copied, and every source also ends the socket's receiving (`tcp_reset`/`tcp_write_err` → `tcp_done`: `sk_shutdown = SHUTDOWN_MASK`) | yes: every case, 0 unread at the error, EOF after it |
| `timeout` | a read deadline (Go's `prepareRead`/`waitRead`, before or instead of `read(2)`; the socket untouched) | **no** (`TestStickyNotTimeout`): bytes may follow once the deadline is cleared or moved |

No other non-sticky case was found. Not tested (and not modelled as sources of a `sys` read error
on a connected socket): `IP_RECVERR` (Go never sets it; without it ICMP errors on an established
socket are soft), `SOCK_DESTROY`/`ss -K` (an administrator's; outside the closed world, D13),
`ENOMEM` (D12).

**After a read error, `Write`:** EOF from a FIN leaves the reader's own direction open: its `Write`
succeeds (`TestStickyEOF`); after a `sys` read error every `Write` fails `EPIPE`; after `closed`,
`ErrClosed`; after a `timeout`, it succeeds. The model already allows each (`WriteOutcome`: after a
read's cut the writer's own direction may still be open in the model, where a `Write` may succeed:
more than Linux, sound). **The rule does not touch `Write`.**

**The conformance checker's recorded real runs** (`examples/net/conform/testdata`, 15 runs): with
`model.py`'s and `lazy.py`'s `sys` clause narrowed the same way (a scratch copy, not committed),
all 15 are still ADMITTED; the checker's own unit test `test_break_prefix_reset_eof` (a synthetic
trace: `abc` read, `sys`, EOF, with `def` written and never read) then fails, the witness builder
still placing the cut at the EOF; under the new rule the trace is allowed with the cut at the `sys`
read keeping nothing, so that test's expected witness (`cuts == [3, 0]`) and the builder change
with the semantics.

## With this change

### The rule

D1, `ReadAvail`'s `sys` clause gains `d.bytes = []`:

```lean
  -- an error, once the connection broke and nothing is unread
  (d.status = .cut ∧ d.bytes = [] ∧ r = .err .sys ∧ d' = d) ∨
```

That is the whole change to the trusted text (plus D1's prose). The break clause is unchanged: a
read may still cut the direction and answer `sys`, but then it keeps the empty prefix (the unread
bytes are lost, as a RST that arrives before they did loses them), or it keeps some and answers
with the first of them (what Linux does: the received bytes come first).

What it gives, as a derived fact (no new state): call a direction **dead** when nothing is unread
and it is not open (`NetDir.dead d := d.bytes = [] ∧ d.status ≠ .open`).

* A `Read` that returns EOF or `sys` leaves its direction dead (EOF already; `sys` now).
* Every outcome keeps a dead direction dead (`ReadOutcome`, `WriteOutcome`, `CloseOutcome`,
  `CloseWriteOutcome`: a dead direction gets no byte, and `shut` keeps a status that is not open).
* On a dead direction a `Read` of `n > 0` returns no byte: EOF, `sys`, `timeout` (with a read
  deadline set) or `closed` (once the end is closed); `n = 0` returns `(0, nil)` (Go:
  `TestStickyReset`'s empty read).

So: **after a `Read` returns EOF or a `sys` error, every later non-empty `Read` of that end returns
no byte, with an error** (EOF, `sys`, `timeout` with a deadline, or `closed` after a `Close`).
Which error: Linux returns EOF after `ECONNRESET`/`ETIMEDOUT`/`EHOSTUNREACH` (the error is
consumed once, `sock_error`), and EOF after EOF; the model allows EOF or `sys` (more than Linux,
sound: the proofs above `Read` treat any error alike) and, with a read deadline set, the timeout
(Linux: `TestStickyReset`'s expired deadline gives `timeout`, Go's check before `read(2)`). After
`closed`, `closed` (already). A `timeout` is not sticky: it changes nothing (`d' = d`), as before.

**Soundness.** The rule removes exactly the traces in which a `sys` read error comes while a byte is
still unread in the model's direction. Every Linux trace stays allowed: Linux returns an error from
`read(2)` only when it copied nothing (`tcp_recvmsg_locked`), so the model's run cuts the direction,
at that read, keeping exactly the bytes the kernel had received and the program has read (none
left: the break clause with `k` the received count, the earlier reads having taken them), and the
bytes still in flight are lost, which no later Linux read can return either (the socket is done).
The 15 recorded runs of the conformance checker are still admitted (above). Nothing else narrows:
EOF, `closed`, `timeout`, every `Write`, `Close`, `CloseWrite`, `Accept`, `Dial` are untouched.

**Why no `NetConn` field.** The stickiness is recorded by the direction itself (dead: cut or fin,
empty), which no step undoes, so the semantics needs no new state. The alternative, a field
`NetEnd.rfail : Bool` set by a failing read and making every later read fail, puts more into the
trusted text for the same behaviours (and a second fact to keep consistent with the direction:
`rfail → d.bytes = []`); rejected. The proofs get the flag as ghost state instead (below).

### What changes, by file

**`Impl.lean`** (trusted): `ReadAvail` (the clause above); `ReadOutcome`'s docstring; the header's D1
("after a cut, also a `sys` error" → "after a cut, once nothing is unread, also a `sys` error; so no
byte follows a read error but a deadline's timeout"); D14 unchanged; version v3.5 with its history
line. `NetConn`, `NetDir`, `NetEnd`, `NetStep` unchanged. The `isNetStep_total` table's `Read` row
is still "never empty" (a cut keeping nothing, then EOF or `sys`).

**`Specs.lean`**: no statement changes. `Conn.Read.spec` (`Net/Spec/net/Conn__Read.lean`) quantifies
over `ReadOutcome` and keeps its text; `wp_net_op`'s read case is over `ReadOutcome` too.

**`Stream.lean`** (proved): the `rcases` patterns of `ReadAvail`'s `sys` clause in `dirOk_avail`,
`readOutcome_got_le`, `readOutcome_bytes_pos` (`⟨-, rfl, rfl⟩` → `⟨-, -, rfl, rfl⟩`); new pure
lemmas: `NetDir.dead`, `readOutcome_dead_of` (EOF or `sys` leaves `d'.dead`), `readOutcome_dead`
(`d.dead` → `d'.dead ∧ r.got = []`, and `r ≠ .bytes _` for `n > 0`), `writeOutcome_dead`,
`closeOutcome_dead`, `closeWriteOutcome_dead`.

**`Decide.lean`**: `readAvailB`'s `sys` disjunct adds `d.bytes = []`; `readAvailB_iff` (the `err`
case's `simp`), `cut_unique` (the `sys` pattern). `Replay.lean` follows through the deciders,
unchanged.

**`Tests.lean`**: new examples: excluded `ReadOutcome st0 ⟨b3, .cut⟩ 4 (.err .sys) ⟨b3, .cut⟩`
(`TestStickyReset`: no error while bytes are unread); allowed `ReadOutcome st0 ⟨b3, .open⟩ 4 (.err
.sys) ⟨[], .cut⟩` (a cut keeping nothing); `readOutcome_dead` on `⟨[], .cut⟩` (`TestStickyReset`,
`TestStickyTimedOut`). Existing examples hold as they are (line 106's `⟨[], .cut⟩` `sys`; line 585's
`⟨[], .open⟩` read giving EOF or `sys`).

**`Proto.lean`** (proved; the laws the kits and the models' proofs use):

* `ConnPNames` gains `x0 x1 : GName` (`ConnPNames.x s`: the direction from `s` is dead), in `enc`
  and the `Countable` instance; `conn_register` allocates them (a `monoNat` at 0, Perennial's
  `Ghost/MonoNat.lean`).
* `dirSt cn γ s` gains `∃ b, monoNatAuthOwn (γ.x s) 1 b ∗ ⌜b ≥ 1 → d.dead⌝`; `reg_open`'s statement
  carries it (it exposes `dirSt`'s parts; used only inside `Proto.lean`), and each law that writes
  a direction back keeps it by the `*_dead` lemmas.
* New, persistent: `readDead cn s := ∃ γ, connElem cn γ ∗ monoNatLbOwn (γ.x (!s)) 1`: the
  direction towards the end `s` is dead.
* `read_au` is unchanged (its users, about fifteen files in `Net/`, `KvRaft/`, `Dsverify/`, keep their proofs). New
  laws beside it:
  * `read_dead_au` (the update `net.Conn.Read.spec` takes, as `read_au`'s): the same, and the
    result also gives `⌜r = .eof ∨ r = .err .sys⌝ -∗ readDead cn s`;
  * `read_after_dead_au`: from `recvTokL cn s P R ∗ readDead cn s`, the update whose result is
    `recvTokL cn s P R ∗ ⌜r.got = [] ∧ (n ≠ 0 → ∀ bs, r ≠ .bytes bs)⌝`: the reader's position
    stays, and the `Read` returns an error.

**The conformance checker** (a transcription of the semantics, `examples/net/conform/check/`):
`model.py`'s `read_avail`, `lazy.py`'s `sys` case (a `sys` read makes the direction `((), 0, CUT)`),
the witness builder's cut for a `sys` read, `test_check.py`'s `test_break_prefix_reset_eof` (cut
`[0]`), and a new negative test (a `sys` read, then bytes: NOT ADMITTED); `certify.py` re-run on the
sample (Lean's `net-replay`).

**`examples/net/semantics/doc.go`**: the "Sticky read errors" rows become measured evidence of D1
v3.5 (now marked proposed).

### The read-deadline exception, and what the wrappers' removal still needs

The rule leaves a deadline's `timeout` non-sticky, as Linux has it. Each wrapper today also makes a
timeout sticky (`rerr` keeps any frame read error; `connReader.failed` any error but
`abortPendingRead`'s; `connectReader` any error), which is where the models' claims say "but for a
read deadline's timeout". Without the wrapper the model reads on after a timeout as Go does, and a
proof must then show that no timeout happens where Go would misparse: gob's server after a body
read's timeout reads the next header from the middle of a frame (Go does too, over Linux), and
`textproto` after a timeout in the middle of a head line. So removing a wrapper needs, besides
`readDead`, that the end's read deadline is not set: a **read-deadline token** in `Proto.lean`,
`rdlTok cn s b` (exclusive: the end `s`'s read deadline is set, `b`), agreeing with `NetEnd.rdl` in
the registry, given at dial and accept (`b = false`), updated by `deadline_au` (which then takes it:
its statement changes; its users are `lib/remote`'s `attempt` and `serveConn` and Dsverify's paxos
`NetProof`), and a law: with `rdlTok cn s false`, `ReadOutcome` gives no `timeout` (`ReadAvail`'s
fourth clause needs `st.rdl`). `net/http`'s server sets the deadline itself (`abortPendingRead`:
past, then cleared), so its `connReader` proof keeps the token in its mutex invariant and allows the
timeout only while `aborted` (what Go ignores). This part is proof-side only (no trusted change)
and goes with the wrapper removals; it is a design choice for review too (alternatives: a premise
"no read deadline on served connections" in the rpc and http specs, which is what their claims say
now).

### The three wrappers, and when they go

1. **This change** (one branch off `lean`): the rule (`Impl.lean`), `Stream`/`Decide`/`Tests`, the
   checker, `Proto.lean`'s `readDead` and its two laws, the read-deadline token, and **`rerr`
   removed** (`models/net/rpc/codec.go`: `serverCodec` loses `rerr`; `ReadRequestHeader`/
   `ReadRequestBody` call `readFrame` as gob's codec calls its decoder; `Net/` re-translated). Its
   proofs: `serverCodec.ReadRequest{Header,Body}.spec` lose the `rerr ↦ r0` resource and the
   `r0 ≠ nil` case; `rdrOwn`'s failed branch becomes `recvTok cn true (reqProto W a) R ∗ readDead
   cn true` (the reader's position is final: `read_after_dead_au`), with the end's `rdlTok … false`
   in the reader's resources; `Server.readRequestHeader`, `ServeCodec`, `ServeConn`,
   `newServerCodec` follow. A frame longer than `maxFrame` (`errFrame`, the model's own error,
   after which `rerr` also stopped the reads, though the connection did not fail) must then be
   excluded by the protocol (`reqProto`: a model peer's frames fit) or answered as Go answers it
   (the loop ends at the header; at a body, `ServeCodec` reads on).
2. **Right after, on `models-rpc-http`** (where the other two are; or once it lands on `lean`):
   `connectReader` removed (`DialHTTPPath` reads through `bufio.NewReader(conn)`, as Go's does;
   `crSt`/`crErr` become `recvTok` with `readDead` and the dialer's `rdlTok … false`;
   `crErr_final` is `read_after_dead_au`), and `connReader.failed` removed (`Read`,
   `backgroundRead` as Go's; `ConnReader.lean`'s `crBg`/`crOwn` lose `failed`, keeping `readDead`
   once a read failed, and the `rdlTok` as above). Their claims widen: a `Server` with
   `ReadTimeout`/`ReadHeaderTimeout`/`IdleTimeout` is then Go's behaviour too, given a proof that
   handles the timeout (or the premise).

The order matters only in that the second needs the first's laws; the semantics change can also
land alone first (no wrapper removed), since every existing proof keeps working over the narrower
relation (only the pattern fixes in `Stream`/`Decide`).

### Risk

* **Trusted**: one conjunct in `ReadAvail`, which only removes behaviours; the risk is that it
  removes one Linux has. The evidence above covers every source of a `sys` read error on a connected
  socket in configuration C; the recorded real runs are still admitted.
* **Proofs that may break**: in the semantics' own files only: `Stream.lean` (three `rcases`),
  `Decide.lean` (`readAvailB_iff`, `cut_unique`), `Tests.lean` (examples that unfold `ReadAvail`:
  checked by reading, none states a `sys` read with bytes unread). No proof outside
  `GooseLang/Ext/Net/` unfolds `ReadOutcome` or `ReadAvail` (grep, 2026-11-23); they use
  `readOutcome_got_le`, `readOutcome_bytes_pos`, `readOutcome_of_closed`, `dirOk_read`, whose
  statements do not change. `Proto.lean`'s internals change (`dirSt`, `reg_open`, `conn_register`
  and the laws that write a direction back), no external statement but `deadline_au`'s (the token).
* **Rebuild**: `Impl.lean`'s change rebuilds every module over the net extension (`Net/`, `KvRaft/`,
  `Dsverify/`, the single-process theorems).
* **The wrappers' proofs**: `rerr`'s removal touches the rpc server's reader invariant and five
  specs; the `errFrame` case is the open question there.

## Implemented (2026-11-23, branch `net-sticky-read`)

**Trusted** (`GooseLang/Ext/Net/Impl.lean`, v3.5): `ReadAvail`'s `sys` clause is
`d.status = .cut ∧ d.bytes = [] ∧ r = .err .sys ∧ d' = d`, as planned; D1's prose and the version
history say why. `examples/net/semantics/doc.go`'s "Sticky read errors" rows are D1 v3.5's
evidence, with a v3.5 paragraph. `etc/gates.sh` runs the loopback sticky tests (`net-sticky`; the
network-namespace one needs root and skips there).

**Proved, pure** (`Stream.lean`): `NetDir.dead`, `readOutcome_dead_of`, `readOutcome_dead`,
`writeOutcome_dead`, `closeOutcome_dead`, `closeWriteOutcome_dead`, and `closeOutcome_rdl`,
`deadlineOutcome_w_rdl`, `deadlineOutcome_closed`, `readOutcome_closed_of`, `readOutcome_closed`,
`readOutcome_no_timeout`. `Decide.lean`'s `readAvailB` and `cut_unique`, `Tests.lean`'s patterns
and three new examples (no `sys` with bytes unread; a cut keeping nothing, then `sys`; a dead
direction reads EOF or `sys` again). The conformance checker (`model.py`, `lazy.py`, `replay.py`'s
witness builder: a `sys` read cuts keeping nothing; `test_break_prefix_reset_eof` now `[0]`; a new
negative test `test_bytes_after_sys_read_error`); its unit tests and `go test ./net/conform/check/`
(the 15 recorded runs) pass.

**`Proto.lean`** (proved; differs from the plan where marked):

* `ConnPNames` gains `x s` (a direction's dead counter, `monoNat`), `d s` (an end's read deadline,
  a ghost variable) and `c s` (an end's closed counter, `monoNat`; **not in the plan**). `dirSt`
  keeps `1 ≤ x → d.dead`, `endSt` (now with `γ`) a half of `d s` at `st.rdl` and `1 ≤ c →
  st.closed`. `reg_open_full` exposes all of it; `reg_open` keeps its shape, its closer also asking
  that the read deadline is kept, a dead direction stays dead and a closed end closed.
* `readDead cn s` (persistent): **the direction towards `s` is dead, or the end `s` is closed**
  (the plan had only the first). A served connection's reader gets `closed` if the end is closed,
  and the proofs have no exclusive knowledge that it is not; `closed` is sticky too (D3), so it is
  a reason a read returns nothing more, and the law covers it.
* `rdlTok cn s b` (exclusive): the end's read deadline is `b`; it holds `regCtx`. **Given by
  variants of the laws**, `dial_rdl_au`, `accept_rdl_au`, `accept_shared_rdl_au` (and internally
  `accept_au_at`, `accept_shared_au_at`, `pendRes_take`, `conn_register`), not by `dial_au`/
  `accept_*au`, whose statements are unchanged (they are derived from the variants, dropping the
  token), so that their twenty-odd users do not change.
* `read_dead_au cn s P R n b`: from `recvTokL ∗ rdlTok cn s b`, `read_au`'s update, which also
  gives the token back, `st.rdl = b` in its outcome fact, and `⌜r = .eof ∨ r = .err .sys ∨ r = .err
  .closed⌝ -∗ readDead cn s`. `read_after_dead_au`: from `recvTokL ∗ readDead`, the update whose
  result keeps the reader where it was and returns no byte. `read_au` is unchanged.
* `deadline_au cn s k set b`: **takes `rdlTok cn s b` instead of `connIs`** and gives back
  `rdlTok cn s st'.rdl`; `deadline_w_au` (new): the write deadline (kind 2) with `connIs` only, as
  it leaves the read deadline as it is. Users: lib/remote's `attempt` (`dial_rdl_au`) and
  `serveConn` (its spec takes `rdlTok cn true false`, which `Serve` gets from `accept_rdl_au`);
  paxos's `writeFrame` (`deadline_w_au`) and `readLoop` (its spec takes `rdlTok cn true false`, kept
  as `∃ b, rdlTok` in the loop; `acceptLoop` uses `accept_rdl_au`). No top-level statement changed.

**Not done: `rerr`'s removal** (`models/net/rpc/codec.go`). What it needs, found while starting
it:

1. **The failing read's fact through the frame readers.** `readFull`/`readFrame` and the codec's
   four read specs take an update returning `P (got ++ r.got)`, which forgets `r`; the server needs
   `readDead` exactly when a read failed. Proposed: a parameter `F` (the update returns
   `P (got ++ r.got) ∗ (⌜∀ bs, r ≠ .bytes bs⌝ -∗ F)` and the error post gives `F`); the client's
   callers pass `F := True` (`Client__input`'s `rd_acc` wrapped once).
2. **`errFrame`.** Go's gob reads on after a too-long message (its `recvMessage` sets `errBadCount`,
   reset by the next `Decode`), from inside it; `ServeCodec` ends the loop at a header's error but
   reads on after a body's (`keepReading`), so Go then parses the frame's payload as frames, which
   no proof can follow. Following Go is therefore not provable; excluding such frames by the
   protocol needs `reqOk` to bound a request's header and body by `maxFrameN` (today `< 2^63`), and
   a model client cannot know that of `Encode`'s bytes without a check: proposed, the model's
   `clientCodec.WriteRequest` returns `errFrame` without writing for a frame longer than `maxFrame`
   (gob's encoder also refuses a message of `tooBig` bytes, but leaves the header it already
   encoded in its buffer for the next flush, which the model would not model: a gap the package doc
   would state), and `reqUpd`'s premise gives the bound. A decision for the user.
3. Then as planned: `rdrOwn`'s failed branch `recvTok … R ∗ readDead cn true`, the reader's
   `rdlTok cn true false` (`rpcAccepted`, from `accept_shared_rdl_au` in `Server.Accept`), the five
   specs and `newServerCodec`; `models/internal/rpcdifftest/run.sh`; `models/README.md`'s net/rpc
   row; `nonissues/go-netrpc-server-reads-on-after-body-read-error.md` closed.


## Part 2 implemented (2026-11-24, branch `net-rpc-rerr`)

The user's option (B) (#24): `rerr` goes; a too-long request frame is the model's stuck point, not a
silent refusal (the model keeps every Go behavior: gob leaves the header buffered); `reqOk` bounds a
request's frames by `maxFrameN`. Ledger 2026-11-24.

* **The model** (`models/net/rpc/codec.go`): `serverCodec` has no `rerr`; `ReadRequestHeader`/`ReadRequestBody`
  call `readFrame` as gob's codec calls its decoder. `clientCodec.WriteRequest` encodes the body, then calls `stuck()`
  when the header or the body is longer than `maxFrame`; `stuck` (Go body `select {}`) is trusted
  (`Net/Code/net/rpc.toml`, `Net/TrustedCode/net/rpc.lean`: Perennial's `internal.gomodel.Stuck.impl`, at the current
  pin `580868e54` already in Perennial's `TrustedCode/internal/gomodel.lean`; its proof scaffolding, `ed1955557`, is not
  needed). `models/internal/rpcdifftest/run.sh` passes (real and model).
* **Where the bound comes from.** `Client.Call.spec` (and `Go`, `send`, `WriteRequest`) takes
  `⌜sm.length + 16 ≤ maxFrameN⌝` and the arguments' encoding with `⌜bs.length ≤ maxFrameN⌝` in its continuation: the
  caller proves it of its own encoding (no codec bound in `encOk`: a generated codec's encodings are not bounded in
  general, and only the caller knows its arguments). The landed kits prove it of their concrete arguments (swiftpaxos:
  `client.Client.call.specI` gains the premise, its callers' arguments are constant; `Register`'s address is one of
  `replicaAddrs`; epaxos's `wp_Call_simple`). gryff and craq (not landed) must adapt the same way.
* **The reads keep the failing result**: `readFull`/`readFrame` and the server codec's read specs take `F` (the
  accessor's `⌜∀ bs, r ≠ .bytes bs⌝ -∗ F`; a `readErr` comes with `F`); the client passes `F := True`
  (`readAcc_true`), the server `readDead cn true` (`rd_acc_dead`, from `read_dead_au` with the end's
  `rdlTok cn true false`; `readOutcome_no_timeout` rules out the timeout). Once dead, the reader reads through
  `rd_acc_after` (`read_after_dead_au`): nothing, and the next header fails, ending the loop.
* **`errFrame` at the server**: `readFrame`'s `errFrame` after a long length now gives those 8 bytes, which the
  protocol makes the next payload's length (`framesOf_next_len`, `reqPlsFrom_fit`, `req_len_fit`): at most
  `maxFrameN`, so the body's `errFrame` is excluded; a header's error ends the loop anyway.
* **Over HTTP** (not in the plan): the hijacked connection's read deadline token was `∃ b` (`hijackOk` did not hand it
  to the handler). The model's `hijackLocked` clears both deadlines; `deadline_dead_au` (new, `Proto.lean`) gives the
  token at the outcome and `readDead` when the setting fails on a closed end, so `hijackOk` hands the handler
  `∃ b, rdlTok cn true b ∗ (⌜b = false⌝ ∨ readDead cn true)` and `rpcAccepted` holds `rdlTok cn true false ∨
  readDead cn true`.
* No top-level statement changed (`TopLevelRobustness`, `TopLevelDefs`, `Net/Statement` untouched).
