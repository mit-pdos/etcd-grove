# Clients on machines of their own: porting dsverify-lab's `Remote` (plan)

Claim: etcd-grove#24 (etcd-dist, D8). Session: agent of etcd-grove-03 for kaashoek, branch `remote`,
worktree `/shared/etcd-grove-remote`. Started 2026-11-21.

The user's design is dsverify-lab's (`notes/clients-separate-nodes.md` there, decided 2026-11-17: spec
(R), a fixed client per operation sequence): a test's clients run as processes of their own, so that no
proof can use the fact that they share a process (a prophecy, a lock, a package variable that sees every
client's steps in one order). Node 0, the **orchestrator**, generates the operations, records the history
and checks it. **Client node c** runs client c's operations with the system's client library and answers.
This plan ports that design onto etcd-grove's net extension as a neutral library, `examples/lib/remote`.
dsverify's kits (phase 6 of `notes/dsverify-net-port-plan.md`) can reuse it, and so can etcd-dist's
workloads (`notes/etcd-dist-plan.md` §2, D8).

**Status:** R0 reviewed 2026-11-22; this is revision 2, after the coordinator's decisions (§8). **R1 done** (2026-11-22, §5). **R2, R3: see "R2 and R3"** (2026-11-22). **R4 done** (2026-11-22, "R4, done" at the end): `counter_remote_robust`, closed.

## 1. The lab's pieces, mapped to ours

| Lab (dsverify-lab `master`) | Here | How |
|---|---|---|
| `harness/remote/remote.go`: `Call`, `Serve`, `ServeClient`, `RunRemote`, the wire, `Codec`, `String` | `examples/lib/remote/remote.go` | **ported, changed** (§3): one connection per attempt; a write gets one attempt and otherwise an unknown outcome, a read up to `ReadTries` attempts; the codec gains `IsRead` and `Unknown`; no `configure`/`New`, `Start` or `waitMs` |
| `harness/driver` (`driver.Run`: client goroutines, `Gen`, `Start`, the recorder) | `examples/lib/lintest`, through a new package `lintest/perclient` whose `Run`'s `apply` gets the client id (Q1); lintest itself unchanged | **reused** |
| `Recorder.lean`, `RunInv.lean`, `ClientSpec.lean`, `Driver.lean` | lintest's `Defs`/`InvLemmas`/`RunLemmas` (`applySpec`, `genSpec`, `clockSpec`, `linInv`) | **reused**. The lab's `opAwpMaybe` (commit, or an error after which the update may still fire) **is kept**, as the client node's obligation (§4). Node 0 turns it into lintest's always-committing `applySpec` over a model with pending writes |
| `CheckerSpec.lean`, `PorcupineLin.lean`, the porcupine **axiom** | `Proof/github_com/anishathalye/porcupine/` (verified, no axiom) through lintest | **dropped**: our proof replaces it |
| `Remote/RunP.lean`, `DriverP.lean` (the driver's proof copied for persistent commit postconditions only) | none | **dropped**. The committed continuation comes back to the caller through the slot invariant (§4), so lintest's `applySpec` is proved for any postcondition |
| The lab's unknown outcomes (porcupine's pending operations, through its axiom) | the pending-writes model `linkv.PendSpec`/`pM` (`Proof/.../etcd/txnlin/PendModel.lean`, used by txnlin and k8s etcd3) | **reused**. A failed write is pending: it may take effect later, at most once, or never. A failed read constrains nothing |
| `Remote.lean`: `slotReg`, `reqProto`, `repProto`, `RemoteNames` (per-(c, j) claim tokens and saved predicates, allocated at the start for `j < k`) | `Remote/Defs.lean` | **redesigned** (§4): one slot per connection, made by the dialer once it has the connection and claimed by the acceptor with that connection's `connFresh`. No `j`, no `k`, no start allocation per operation |
| `Remote/Wire.lean` | `Remote/Wire.lean` | **ported** to kvnet's frame format, with prefix lemmas (§2) |
| `Remote/Call.lean`, `Serve.lean`, `RunRemote.lean`, `Init.lean` | `Remote/{Call,Do,Serve,ServeClient,Run,Init}.lean` | **re-proved** over the net extension's canonical specs (`Net/Spec/net/`) and `GooseLang/Ext/Net/Proto.lean` (`dial_au`, `accept_au`, `writeP`/`write_acc`, `read_au`, `close_au`, `deadline_au`) |
| `Remote/Codec.lean` and the per-model codecs (`CodecKV`, `CodecCasReg`, `CodecKVScan`, ...) | `Remote/Codec.lean` (`CodecSpec`) and one codec per instance | **ported in form**. R4 gets the counter's codec. The lab's codecs are not ported (their models are the lab's) |
| `Remote/Start.lean` (`remote_start`), `Dist.lean` (`remoteDistSafe` over `SafeDist`), `DistSha.lean` | `Remote/Start.lean`, `Remote/Robust.lean` (`remote_robust`) | **re-stated** as `DistDeploy … → Robust [] …` through `robust_of_distProto` (§6). SHA is not needed |
| `RemoteKit`, `RemoteFacts`, `RemoteMainFacts`, `remoteMainImpl`/`clientNodeImpl` (`rfl` facts about kitgen's generated `Main`) | none | **dropped**. An instance proves its nodes' boot WPs itself, calling `remote.Check`'s and `remote.ServeClient`'s specs |
| `Mux.lean` | not used by `Remote` | not needed |
| kvnet's `kvcheck` (#22) | not edited | **reused as the reference** for the client side: one request frame per connection with a timeout, the frame format. Not imported: `remote` must not depend on kvnet |

## 2. Semantics: the lab's `NetConn` vs the net extension

| Difference | Lab | Here | What it means for the specs |
|---|---|---|---|
| Errors | codes | kinds `closed \| timeout \| sys`, EOF a read result (`ReadOutcome`) | none. Every error is a failed attempt, so no spec has an error predicate |
| `Write` | one step | a loop of steps (D15): may write a prefix, then fail | a reader can see a truncated frame. The protocols are prefix-closed (`protoPrefix`, `ProtoPrefixClosed`), and a frame carries its length, so a reader that gets a whole frame gets the one that was written (`Wire.lean`: no frame is a proper prefix of another). A truncated frame fails `readFull`, and the reader closes |
| Write lock (D25) | not modeled | a waiting `Write` step may stutter | none: one writer per end |
| Read facts | immediate | one step later (`recvTokL`, `recvTokL_later`) | later credits in the read loop, as `wire.ReadFull`'s proof already does |
| Abandoned dials (D16) | no | `Accept` may return a connection whose dial failed (an empty, shut direction) | `Serve` reads EOF and closes. No slot was made for it, and none is claimed |
| Deadlines | timeouts | the value is not modeled: any operation may time out once a deadline is set (`deadline_au`) | a timeout is a failed attempt. Timing is never used for safety |
| `Listen` | needs an exclusive address token | `addrTok` persistent; `Listen` on an address in use fails with `sys`; listening token `netLisTok` (v3.4) | `Serve` retries `Listen` (as the lab's and kvnet's do). A listening node's share includes its address's `addrUnset` and protocol |
| Deployment | `cfg.WellFormed`, plan, hosts | `DistDeploy addrs nodes g` (v3.4): addresses distinct and `addrOk`, no connections, no listeners | the addresses are the listening nodes' (client nodes, servers). Node 0 listens on none |
| Crashes | none (`SafeDist`) | `Robust crashing stable`. The kits use `Robust []` (`robust_of_distBoot`) | the orchestrator and the client nodes are **stable** (they keep the history). R3 proves the `Robust []` form. Each node's boot WP is a separate lemma, so a mixed bridge (crashing servers: #22's `NetFs` adequacy, etcd-dist D3) can reuse them unchanged |
| Liveness | not proved | not proved | a call that never gets a reply waits for its attempt's deadline. Safety only |

No change to the net extension or to Perennial. Everything above uses specs and laws that exist
(`Net/Spec/net/{DialTimeout,Listen,Listener__Accept,Conn__Read,Conn__Write,Conn__Close,
Conn__SetDeadline}.lean`, `Proto.lean`, Perennial's `time.Now`, `Time.Add`, `sync/atomic`, and
goose's `primitive.NewProph`/`ResolveU64`, as txnlin uses them).

## 3. The Go API (`examples/lib/remote`)

```go
// Codec: a model's inputs and outputs as bytes (Dec* false on bytes that are not an encoding),
// which inputs are reads (a read may be retried; a write may not), and the model's unknown
// output for an input (txnlin's Output{Err: true}).
type Codec struct {
	EncIn   func(any) []byte
	DecIn   func([]byte) (any, bool)
	EncOut  func(any) []byte
	DecOut  func([]byte) (any, bool)
	IsRead  func(any) bool
	Unknown func(any) any
}

// Node 0: perclient.Run (lintest's driver) with apply(c, in) = Do(addrs[c], in, codec, attempt); porcupine checks the
// history against model.
func Run(model porcupine.Model, addrs []string, codec Codec, gen func(int) any, ops int,
	attempt time.Duration, timeout time.Duration) porcupine.CheckResult
// Check is Run with no timeout; it panics unless porcupine answers Ok (the theorem: it never panics).
func Check(model porcupine.Model, addrs []string, codec Codec, gen func(int) any, ops int,
	attempt time.Duration)

// One operation at the node listening at addr: a write gets one attempt, a read up to ReadTries.
// It returns the output the far side answered, or codec.Unknown(in) if no attempt got an answer
// (or the far side answered "unknown": its own operation failed).
func Do(addr string, in any, codec Codec, attempt time.Duration) any

// The node at addr: listens (retried), serves one connection at a time with op(sys, in). It never
// returns. ServeClient(c, ...) is newClient(c), then Serve.
func Serve(addr string, sys any, op func(sys any, in any) any, codec Codec)
func ServeClient(c int, addr string, newClient func(int) any, op func(sys any, in any) any, codec Codec)
```

**The wire.** kvnet's frame format: an 8-byte little-endian length, then the body. One connection
per attempt, carrying one request and at most one reply:

- the request is the frame `in`;
- the reply is the frame of `EncOut(out)`. The unknown output is a model output like any other,
  so it is encoded too: an `op` that returned `Unknown(in)` replies with it, and the caller
  returns it.

There are no sequence numbers. An attempt is identified by its connection.

**`Do`** runs, for each attempt:

1. `DialTimeout`, then `SetDeadline(now + attempt)`;
2. write the request, then read the reply;
3. if the reply decodes, return it (it may be the far side's unknown output).

On any failure, a read tries again
(at most `ReadTries` attempts, 3), and a write stops after its one attempt. Either way, when no
attempt gets an answer, `Do` returns `Unknown(in)`. A prophecy (`NewProph` at the start of `Do`,
`ResolveU64` at its end) records which attempt answered **with a known output** (or none). It does
nothing in Go; node 0's proof needs it (§4).

**Why the far side may answer "unknown", and `Codec.IsUnknown`.** The far side's `op` may itself fail
to learn its operation's outcome, and then returns `Unknown(in)`, which `Serve` encodes and sends like
any output. This happens in R4: a client node's `op` is a `Do` to the server, whose reply may be cut
after the server applied the increment. The far side's update may then have fired (its `Φ` dropped
there), may fire later, or never: for node 0 the call's outcome is unknown, as when no reply arrives.
Node 0 commits lintest's operation *before* the call for an outcome that will be unknown (as pending),
and *at the far side's step* for one that will be known, so it must know which before the first
attempt: the prophecy names the attempt answered with a known output, and `Do` tells the two apart
with `Codec.IsUnknown` (true of `Unknown(i)`'s values, false of the model's outputs). An attempt
answered with the unknown output resolves the prophecy as "none".

**`Serve`** handles one connection at a time:

1. accept, then `SetDeadline`;
2. read the request frame and decode it;
3. run `op(sys, in)`;
4. reply `EncOut(out)`, unless the encoding is longer than `MaxLen`;
5. close.

A connection whose request does not arrive whole, or does not decode, is closed without running
anything.

**A write whose connection is cut mid-call.** If the cut comes before the client node has read the
whole request, the client node never runs it: the write has no effect, now or later. If the cut
comes after, the client node runs `op` to completion (it is not cancelled), then fails to write
the reply, closes and serves the next connection. The write may have taken effect, or may still
take effect later through the far side's own pending state (an etcd proposal still in raft).

In both cases node 0's `Do` sees a failed attempt and returns `Unknown(in)`. The model takes that
as a pending write: it may have taken effect before the return, may take effect after it (at most
once), or never. Node 0 never resends a write, and no other connection carries it. So nothing
makes writes at-most-once through retries: at-most-once is what one request per connection, and
one claim per connection, give (§4).

**No reply cache, no deduplication.** Revision 1 had both, because it retried writes. Now each
attempt is its own connection and its own slot, and a reply is read on the connection that carried
its request, so a read's retry cannot be confused with a stale reply. `Serve` keeps no state
between connections. This also removes the per-sender deduplication R4's server needed (§6, Q2).

**Too long.** An encoding longer than `MaxLen` (2^20, as kvnet's `maxFrame`) is never sent: node 0
waits forever (`for {}`). No premise (Q4).

**etcd-dist's seam** (branch `etcd-dist` at `59304d8044`, §2 "Stage D1"; not edited). The kv
workload is `RunKV`: `kvClient` (a copy of `lintest.runClient`, made because `Run`'s `apply` gets no
client id) loops over `kvApply(clis[i])`, which is `txnlin.Apply` through client i's own clientv3
client. With `remote`:

- node 0 is `remote.Check(txnlin.Model(), clientAddrs, txnCodec, txnlin.Gen, ops, attempt)`;
- client machine i is `remote.ServeClient(i, addr_i, newClient, op, txnCodec)`.

`perclient.Run` makes the `kvClient` copy unnecessary (D1 can drop it). There is one difference:
`op` must be txnlin's call **without** its prophecies (txnlin's unexported `call`), since node 0's
`Do` now makes the prophecy (§4). txnlin's codec (heap-free `Input`/`Output`, `IsRead` =
`!isWrite`, `Unknown` = `Output{Err: true}`) is etcd-dist's work (§7). The watch/cache writers
(`etcdstart.Writer`) and auth (`auth.Work(cli_who, who)`) are other seams: per-client loops that
are not porcupine histories. `remote` does not cover them (Q6).

## 4. The proof design (R2)

**Where.** In the part `Net/` (it calls `net`, whose main-tree copy is names-only), as a new goose
project `remote`:

- `local=examples/lib/remote`, `root="Net"`;
- `lean_roots` maps `remote` to `Net`, and lintest and porcupine to the main tree (`=`). Checked:
  lintest's 135-module import closure reaches no `net` module;
- specs under `Net/Spec/github_com/.../lib/remote/`, proofs under `Net/Proof/.../lib/remote/`;
- a `Link.lean`, and the collection `etc/tcb-collections/remote.txt`.

**The base and the model.** An instance gives a deterministic base store, `B : linkv.PendSpec St I O`
(`step : I → St → St × O`, `isWrite`, with reads not changing the state), and the base state's
predicate `sysState : St → IProp` over the global ghost state (the far side's: the counter's value,
etcd's KV). The model node 0 checks against is `linkv.pM B dec`: pending writes, as for txnlin, with
`dec` the instance's decoder of porcupine's inputs and outputs (`Unknown(in)` decodes to `err`). The
instance proves `isModel` of its Go model, as txnlin does.

**The far side's obligation** (`opMaybe`: the lab's `opAwpMaybe` over the base, with the node's own
token):

```
∀ sys i Φ, inOk i ∗ tok sys ∗ threadTok ∗
  AU <∀∀ st, sysState st> @ Eop <sysState (B.step i st).1, COMM Φ (B.step i st).2> -∗
  WP op sys i {v, tok sys ∗ threadTok ∗ ((∃ o, v = encO o ∗ Φ o) ∨ v = Unknown i)}
```

Either it committed and returns the step's output, or it returns unknown: the update may then have
fired, may fire later, or never. A library that never fails meets it trivially, for example
`lintest/counter`'s `Counter.Apply`, which is logically atomic over the counter.

**What crosses a connection.** Protocols are persistent, so an update moves through an invariant,
one per connection (the lab's spec (R)):

- **The slot.** After its `DialTimeout` succeeds, the dialer has `cn` and `connFresh cn false`. It
  registers `cn ↦ γ` in a global ghost map (`slotOf cn γ`, persistent). The map's invariant holds
  each registered connection's `connFresh cn false`, so a connection gets one slot. The dialer then
  allocates
  `inv (slotN cn) (pending AU ∨ connFresh cn true ∗ (running ∨ done o (Φ o ∨ takeTok γ)))`.
- **The claim.** The acceptor's `connFresh cn true` (`accept_au`, exclusive, `connFresh_excl`) is the
  only key to the update. The acceptor swaps it for `AU`, so the update fires at most once. That is
  the at-most-once argument, with no sequence numbers.
- **The protocols.** `reqProto cn W`: `W` is a prefix of the frame of `bI i`, with `slotOf cn γ`, the
  slot's invariant and `□ inOk i`. `repProto cn W`: `W` is a prefix of the frame of `bO o`, with
  `slotOf cn γ ∗ doneLb γ o` for an answered `o`, or with `o` the unknown output. Both are persistent.
- **The reply.** After `op` returns `o`, the acceptor stores `Φ o` in the slot (`done`) and replies.
  The dialer, holding `takeTok`, takes `Φ o` when the reply arrives.
- **The spec.** `Do.spec` is `opMaybe` over the same base: the far side's `opMaybe`, transported.
  That is also the obligation of a client node whose `op` is itself a `Do` to a server, as in R4.

**Node 0's `apply` meets lintest's `applySpec` over `pM B dec`.** This generalizes txnlin's
`Inv.lean`: `write_err_commit`, `write_pend_au`, `write_ok_au`.

- A generic invariant `pendInv` relates lintest's `libState S` (half a ghost variable) to
  `sysState st`: some configuration of `S` is `st` with exactly the pending map's writes pending,
  and `S` is closed under late effects.
- `Do`'s prophecy says which attempt answers, if any. Before the first attempt, node 0 decides
  what each attempt's slot holds:
  - the answering attempt's slot gets an update that commits lintest's update with `(i, ok o)` when
    it fires;
  - a write with no answer commits now with `(i, err)` (pending, minting the pending write's token)
    and puts in its slot the update that fires the pending write;
  - a read with no answer commits now with `err` (nothing), and every attempt's slot gets a no-op
    read update (reads do not change the state).
- So lintest's proof, and porcupine's, are used unchanged.

**The cross-node condition** (as the lab's, made explicit). `sysState`, `inOk` and `S.ioOk` are the
same propositions at every node: they are defined over the global ghost state. `CodecSpec` makes
decoding return the value that was encoded, so the model's inputs and outputs must be heap-free Go
values (scalars, strings, structs of them). The counter's `bool`/`int64` qualify; txnlin's
`Input`/`Output` are checked when its codec is written.

**Specs**:

- `remote.Do.spec`: `opMaybe` transported, under the address's protocol;
- `remote.Serve.spec`, `remote.ServeClient.spec`: never return; safe from the node's share and its
  `opMaybe`;
- `remote.Run.spec`, `remote.Check.spec`: lintest's premises (`isModel` with `S.M = pM B dec`,
  `genSpec`, bounds), `CodecSpec`, `pendInv`'s start, node 0's share; then `r ≠ Illegal`, and
  `Check` returns;
- `perclient.Run.spec` (lintest's `Run.spec` with an id-indexed `applySpec`; its proof reuses lintest's `Defs`, `InvLemmas`, `RunLemmas`);
- the frame helpers, ported from kvnet's and `wire.ReadFull`'s proofs, not imported.

## 5. Stages

1. **R1** (done 2026-11-22, below) Go: `remote.go`, `lintest/perclient`, the counter instance, and tests over real sockets
   (loopback):
   - an end-to-end run (node 0, two client nodes, the counter server; porcupine `Ok`);
   - a fault proxy that cuts connections at every byte offset of a request and of a reply, and
     delays and drops. Expected: porcupine `Ok`, with unknown-outcome writes in the history, some
     of which took effect;
   - a differential check against `lintest.Run` with an in-process counter, when there are no faults;
   - a mutation control: a `Serve` that runs a write twice must be caught.

   Also the goose project, `etc/goose.py --check --project remote`, and a gate line.
2. **R2**: translation; `Defs`, `Wire`, frames; `Do`, `Serve`/`ServeClient`; `pendInv` and node 0's
   `apply`; `Run`/`Check`; `perclient.Run`; `Init`, `Link`.
3. **R3**: `remote_robust` (§6), with `remote_start` and the per-node boot lemmas.
4. **R4**: the counter instance, closed, with `#print axioms` and `etc/tcb-collections/remote.txt`.

## 6. The statement (R3) and the instance (R4)

**R3, the generic lemma**, over `DistDeploy` and `DistBridge` as the Net examples (`echo_dist_robust`):

```lean
structure RemoteObligations (orch : Expr × state) (clients servers : List (Expr × state))
    (clientAddrs serverAddrs : List GoString) [G : GooseGlobalGS .hasLC netGF] [NetProtoGS] where
  B : linkv.PendSpec St I O; sysState : St → IProp netGF; inOk …; Eop : CoPset
  Γs : Type
  /-- the instance's start: the base state at B.init and the nodes' shares, from its servers'
  addresses (the harness sets up the client nodes' addresses and the slot map itself) -/
  start : ⊢ regCtx -∗ ([∗list] a ∈ serverAddrs, addrUnset a) ={⊤}=∗
    ∃ γ : Γs, sysState B.init ∗ orchRes γ ∗ ([∗list] c ↦ _ ∈ clients, clientRes γ c) ∗
      [∗list] i ↦ _ ∈ servers, serverRes γ i
  orch_boot : ∀ γ ρ, DistBootWp orch.1 (orchRes γ ∗ remoteOrchShare … clientAddrs ρ)
  client_boot : ∀ γ ρ c m a, clients[c]? = some m → clientAddrs[c]? = some a →
    DistBootWp m.1 (clientRes γ c ∗ remoteNodeShare … a ρ)
  server_boot : ∀ γ i m, servers[i]? = some m → DistBootWp m.1 (serverRes γ i)

theorem remote_robust … (H : ∀ [GooseGlobalGS .hasLC netGF] [NetProtoGS], RemoteObligations …) :
    DistDeploy (clientAddrs ++ serverAddrs) (orch :: clients ++ servers) g →
    Robust [] (orch :: clients ++ servers) g threads bound
```

It is proved by `robust_of_distProto`. `remote_start` sets the client addresses' protocols, allocates
the slot map and `pendInv`, and splits the shares; the instance's `start` does the rest. Each node's
WP is the instance's short proof: it calls `remote.Check.wp_proof`, `remote.ServeClient.wp_proof` or
`remote.Serve.wp_proof` with its model, codec and library. `remote_orch_boot` and
`remote_node_boot` lemmas package the common part. A server that itself listens through `remote`
gets its address's protocol from `remote_start` too: `serverAddrs` are split into `remote`'s and
the instance's own.

**R4, the instance** (Q2 decided): a counter on a server node, behind two client nodes. Four
machines:

- node 0: `remote.Check(model, [c0, c1], codec, gen, ops, attempt)`;
- client nodes 0 and 1: `ServeClient` whose `op` is `remote.Do(serverAddr, in, codec, attempt)`;
- the server: `remote.Serve` with `op` = `lintest/counter`'s `Counter.Apply`, already proved
  logically atomic over the counter.

The model is the counter's pending-writes model: base `B` = increment (a write) or read on an
`int64`. Its Go model is new: its state `(lo, k)` is the counter's least value and the number of
increments pending (the configurations `{(lo + j, k - j)}`), and its `Step` is proved to be
`pSeq.step` on those sets.

Unknown outcomes: a fault proxy in R1's test, and in the proof every attempt may fail. For the
theorem to show an unknown-outcome write, the history itself must contain one, so the workload
includes one: node 0's attempt deadline is short enough that the R1 test sees unknown writes, and
`Check` does not depend on whether they occur. Through `Do`'s two hops, a write can end unknown at
node 0 while it was answered between the client node and the server (the client node's reply cut).
The model then shows it pending and applied.

The statement goes in `Net/Spec/.../lib/remote/counter/TopLevelRobustness.lean`:

`counter_remote_robust.spec := ∀ …, DistDeploy counterAddrs (system …) g → Robust [] (system …) g threads bound`

with `#print axioms` (expected: the net extension's and Perennial's, nothing of `remote`'s), and
`etc/tcb-collections/remote.txt`.

## 7. Sizes

| Piece | Go | Lean (estimate) |
|---|---|---|
| R1 `remote.go`, the counter instance (Go model with pending increments, codec, nodes), tests, fault proxy | ~250 + ~200 + ~400 | — |
| `lintest/perclient` (new package; lintest unchanged) | ~30 | ~350 (`perclient.Run`, `runClient`: lintest's proofs with an id-indexed `applySpec`) |
| R2 `Defs` (slots, protocols), `Wire`, frames | — | ~800 |
| R2 `Do`, `Serve`/`ServeClient` | — | ~1100 |
| R2 `pendInv` and node 0's `apply` (prophecy, pending writes; after txnlin's `Inv.lean`, ~940 lines, without revisions) | — | ~900 |
| R2 `Run`/`Check`, `Init`, `Link` | — | ~300 |
| R3 `remote_start`, boot lemmas, `remote_robust` | — | ~450 |
| R4 the counter's pending model (`isModel`), codec, nodes, `TopLevel*` | — | ~1300 |
| **total** | ~900 | **~5200** (the lab's `Remote*` is ~5700, of which ~1300 is three codecs) |

For etcd-dist (not this branch): txnlin's codec (Go ~150, proof ~500), an exported txnlin call
without prophecies with its `opMaybe` proof (from txnlin's `Apply` proof, which already splits on the
outcome).

Risks:
- **Reads that fire more than once.** txnlin's reads hand the server a *persistent* read update
  (`read_ok_au`: etcd may serve a read's update more than once). `opMaybe`'s update is single-shot.
  If etcd-dist's `op` needs a persistent read update, `opMaybe` gets a read form (a persistent
  update for `B`'s reads, which do not change the state). This is not needed for R4.
- The prophecy's protocol across attempts: the slot contents are decided before the first attempt;
  this needs care in `Do`'s loop invariant. A read's attempts that are not the answering one need
  an update too, since the far side may claim their slots. So `Do.spec` takes, for reads, a
  persistent no-op read update over `sysState` (`readNoop`: `sysState` in an invariant, which
  `pendInv` is), handed to every node in its share. A slot never claims more than its one update.
- Masks: the slot namespace and `pendInv`'s must be outside `Eop` and `lintestN`.
- The build budget: `Net/` is rebuilt by others too. Use the two build slots only.

## 8. Decisions (coordinator, 2026-11-22) and open questions

- **Q1** decided: a separate function whose `apply` gets the client id, with `Run` and its proof
  unchanged. It is in a package of its own, `examples/lib/lintest/perclient` (`perclient.Run`),
  not in `lintest`: any change to `lintest.go` changes its translation's `.olean`, which would rebuild
  2056 modules (327k lines: every lintest user, k8s and etcd included; `etc/importers.py --count`).
  The package beside it changes no existing module.
- **Q2** decided: the counter on a server node behind two client nodes; R4 exercises an
  unknown-outcome write. The decision asked for `Serve` to deduplicate per sender. With one slot per
  connection (§4) deduplication is unnecessary: nothing is resent, and a connection's claim is its
  `connFresh`. **Confirm dropping it.**
- **Q3** decided: the module path beside lintest (`github.com/mit-pdos/etcd-grove/examples/lib/remote`,
  a Go module of its own). The neutral path comes with phase 3.
- **Q4** decided: node 0 hangs on an over-long encoding, with no premise.
- **Q5** decided (the user: "clients in etcd don't retry, except for read ops"): a write that fails on
  the link is an unknown outcome, reported as the model's unknown output (`Codec.Unknown`), never
  retried. A read is retried, up to `ReadTries`. Done in §§2-4.
- **Q6** decided (coordinator, 2026-11-22): later, the non-porcupine workloads (the watch/cache
  writers, auth's principals) also run through `remote`, by an operation "run the client's loop and
  return its report" (each loop on its client machine, node 0 collecting the reports). Not in this
  branch: future work (an `op` whose input names the loop and whose output is its report; `Do`'s
  spec already covers it as a read-like operation with no model state, or a model of its own).
- **Q1, Q2 confirmed** (coordinator, 2026-11-22): `perclient` stays a package of its own, lintest and
  its proof untouched; no per-sender deduplication in `Serve`.

## R1, done (2026-11-22)

- `examples/lib/remote/remote.go` (a Go module of its own; §3), `examples/lib/lintest/perclient`,
  and the instance `examples/lib/remote/counter` (`Model`: the counter with pending increments,
  state `(Lo, K)`; `Codec`; `Gen`; `Orch`, `Client`, `Server`; commands `cmd/{orch,client0,client1,server}`).
- Tests (`counter/counter_test.go`, all pass, also with `-race -count=2`):
  - `TestModelIsPending`: `step` against linkv's construction on explicit configuration sets
    (200k random cases: the same verdicts, and the states stand for the same sets);
  - `TestModelWithoutFaults`: on fault-free histories, the same verdicts as lintest/counter's model;
  - `TestCodec`: round trips, and garbage refused;
  - `TestNoFaults`: the in-process deployment over loopback sockets, porcupine `Ok`;
  - `TestFaults`: fault proxies on both hops, cutting requests and replies at random byte offsets
    and delaying them, ten fresh deployments. Porcupine is `Ok` every time. One run saw 529 cuts and
    174 unknown-outcome increments, of which 80 took effect: the server's count is between the
    answered increments and the answered plus unknown ones;
  - `TestControlDoubleApply`: a server that applies every increment twice is caught (`Illegal`);
  - `TestProcesses`: the four commands as processes, three fresh deployments, the orchestrator exits 0.

  A first version ran several orchestrations against one server, and porcupine rejected the
  history, as it should: the model starts at 0. Each deployment is now fresh.
- Goose: project `remote` (into `Net/`), and `./perclient` added to project `lintest` (lintest's
  other files unchanged). `etc/gates.sh` runs the Go tests (`remote:` line).

## Handoff (2026-11-22, after R1)

**State.** Branch `remote` (pushed), worktree `/shared/etcd-grove-remote`. R0 (revision 2) and R1
are committed. No Lean proofs yet. The translations build (`Net.GeneratedProof...lib.remote*`,
`GeneratedProof...lintest.perclient`: 1584 jobs, 41 s, from an empty `.lake/build` against
`/shared/tmp/manifest-d64.json`). This worktree's `.lake/build` holds that much.

**Next (R2), in order.**
1. **Package facts and initializers.**
   - `Base.lean` for `remote` (`Net/Proof/.../lib/remote/Base.lean`, fact `True`, as `wire/Base.lean`)
     and for `lintest/perclient` (main tree, `Proof/.../lib/lintest/perclient/Base.lean`, fact `True`).
   - The `Init.lean` files come from `etc/gen-init.py` (never by hand):
     - add `github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient` to `ROOTS`;
     - add `remote`, `remote.counter` and `remote.counter.cmd.{orch,client0,client1,server}` to
       `NET_PKGS`, and the four nodes to `NET_PROGRAMS` (package tables).
   - `remote` imports main-tree packages: `lintest`, `lintest/counter`, `perclient`, porcupine,
     `primitive`, `time`, `sync`. Check how `net_inits` treats main-tree packages: `NET_MAIN` only
     covers `os` and the packages it imports. Main-tree non-Perennial packages may need the same
     copying. Run `PERENNIAL_DIR=/shared/perennial-d648cfe22 etc/gen-init.py --check` (the shared
     `.lake/packages/perennial` is absent here).
2. **Frame helpers.** `readFull` is `wire.ReadFull` verbatim: port `Net/Spec|Proof/.../net/wire/ReadFull.lean`.
   `writeAll` follows `Conn.Write.spec` with `writeP`/`write_acc`. Then `writeFrame`/`readFrame`
   with `Wire.lean` (`le64`, a frame is not a proper prefix of another).
3. **The slot library** (`Defs.lean`, §4): the slot map `cn ↦ γ` holding the dialers' `connFresh cn
   false`, the slot invariant, `reqProto`/`repProto` (prefix-closed), and the laws (register, claim
   with `connFresh cn true`, done, take).
4. **`attempt`, `Do`** (`opMaybe` transported; the prophecy unused there); **`serveConn`, `Serve`,
   `ServeClient`**.
5. **`pendInv`** (generic over `linkv.PendSpec`; model it on txnlin's `Inv.lean`, without revisions)
   and node 0's `apply` (prophecy cases), then **`perclient.Run`** (lintest's `Run` proof with an
   id-indexed `applySpec`) and `remote.Run`/`Check`.

**Pitfalls.**
- Build only through `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-d64.json build …`.
  `etc/goose.py` cloned Perennial into `.lake/goose/perennial` (fine). `PATH` needs `/usr/local/go/bin`.
- Never touch `lintest.go`: its translation's `.olean` is imported by 2056 modules.
- In-process Go tests must use fresh ports per deployment: a `Serve` never returns, and an earlier
  deployment's server keeps its state (porcupine then rightly says `Illegal`).
- Reads' non-answering attempts need a no-op read update (§7, risks): plan `Do.spec`'s read premise
  before proving `Do`.
- For etcd-dist: its `op` must be txnlin's call *without* its prophecies, and txnlin's reads may
  need a persistent read update (§7).

## R2 and R3 (2026-11-22)

**A design change: `Codec.IsUnknown`.** The far side may *answer* the unknown output (its own
operation failed, e.g. a client node whose `Do` to the server got no answer). Then its update may
have fired and its `Φ` been dropped, so node 0 cannot have handed it the update that commits
lintest's operation with an answer: node 0 must know, before the call, whether `Do` will return a
known output. The prophecy now says which attempt is answered **with a known output**
(`ResolveU64(tries)` also when the answer is the unknown output), which `Do` tells by a new codec
function `IsUnknown` (the counter's: `out.(Out).Unknown`). Go and its tests updated; translation
regenerated. Without it R4's two hops are unprovable (a reply of `Out{Unknown}` from a client node
whose write fired at the server).

**Files** (`Net/Proof|Spec/github_com/mit_pdos/etcd_grove/examples/lib/remote/`):

- `Base.lean`, `Init.lean` (generated: `etc/gen-init.py`, `remote` in `NET_PKGS`; lintest's, perclient's
  and porcupine's `Init.lean` copied into the part through `NET_MAIN`, since the main tree's import
  the main `PkgInitExt`), `Pkg.lean` (`io.EOF`, `ErrDeadlineExceeded`, `errTimeout` from `remote`'s
  initialization).
- `Wire.lean`: `frame`, `maxLen`, `frame_prefix_eq`.
- `Defs.lean`, **the slot library**: `RBase` (the far side's store `B : linkv.PendSpec`, `sysState`,
  `Eop`, the Go values `iv`/`ov`/`unk` and bytes `encIn`/`encOut`), `lin R i Φ` (the step's update,
  a plain fancy update as lintest's), `slotOf`/`slotInv`/`runTok`/`doneLb`, `mapCtx` (the slot map,
  holding every registered connection's dialer `connFresh`), `reqP`/`repP`/`remoteAddr`, `codecOk`,
  `opMaybe`; laws `slot_register`, `slot_claim` (the acceptor's `connFresh` stays in the slot: at most
  once), `slot_done`, `slot_take`, `req_read`, `rep_read`. Claim, done and take take a later credit.
- `Pend.lean`, **node 0's pending writes**: `pendCtx R S γ` (global, allocated at the start:
  `pend_alloc`), lintest's `libState` = `pendLib` (a history in a ghost variable: a model state is not
  countable), `PendDec` (porcupine's model is `pSeq R.B` on `R`'s values), `readNoop`, `pend_fire`,
  and `pend_choice`: lintest's update (with a credit) gives exactly `Do.spec`'s choice premise.
- Specs and proofs: the frame helpers (`putU64`, `getU64`, `writeAll`, `readFull`, `writeFrame`,
  `readFrame`; `FramesLinked.lean` closes them over the net package's proofs), `hang`, `deadline`,
  `attempt`, `Do`, `listen`, `serveConn`, `Serve`, `ServeClient`, `Run`, `Check`.
- `Do.spec`: the caller's choice `∀ known, |={⊤}=> if known then lin R i Φ else Ψ ∗ lin R i (λ _, True)`,
  applied at `Do`'s prophecy; reads also take `□ lin R i (λ _, True)` (other attempts). Post:
  `(∃ o, v = ov o ∗ Φ o) ∨ (v = unk i ∗ Ψ)`. A client node whose `op` is `Do` meets `opMaybe` from it
  (`Ψ := True`).
- `Run.spec`: lintest's conclusion under `PendDec`, `pendCtx`/`pendLib` at the model's start, the
  masks `pendN ⊥ Eop`, `lintestN ⊥ Eop ∪ pendN`, `receiptBound GF ≤ 2^63` (lintest's clock).
- `perclient` (main tree): `applySpecId`, `runClient`/`Run` proved, `Link.lean` (`etc/gen-link.py
  --perclient`, list `etc/link-lean-first-perclient.txt`).
- `Robust.lean` (R3): `remote_start` (slot map; every address's protocols for a store chosen
  later) and `remote_robust`: `DistDeploy addrs nodes g → Robust [] nodes g threads bound` from the
  instance's update (registry, slot map, the address-setting capability ⟹ a share per machine with
  its `DistBootWp`), through `robust_of_distProto`. All addresses are `remote`'s (R4's are); an
  instance address of its own protocol is future work. No generic boot lemmas: each node's WP is the
  instance's (`Check.spec`, `ServeClient.spec`, `Serve.spec` at its `main`).

- `Link.lean`: every function linked (`wp_Check`, `wp_ServeClient`, `wp_Serve`, `wp_Do`, ...);
  `#print axioms` of each, and of `remote_robust` and `pend_choice`: `propext`, `Classical.choice`,
  `Quot.sound` only. Its section takes `[NaInvG GF]` (porcupine's, through perclient).
- `Run.spec`/`Check.spec` take `∀ st, Timeless (R.sysState st)`: node 0's invariant is opened inside
  `lin` and in `readNoop` (persistent), where no later credit is at hand. The counter's state (a ghost
  variable) is timeless (`cR_timeless`, R4). **When kv (txnlin, etcd-dist) moves onto `remote`, etcd's
  KV state (its `sysState`, `etcdKV`) must be shown timeless** (coordinator, 2026-11-22).

No axiom, no `sorry`, no change to the net extension or Perennial. (A Perennial tactic gap found on the
way: `notes/perennial-changes.md`, 2026-11-22, `wp_apply`'s silent `sorry`.)

## R4: the statement (approved by the coordinator, 2026-11-22)

`Net/Spec/github_com/mit_pdos/etcd_grove/examples/lib/remote/counter/TopLevelRobustness.lean`:

```lean
/-- The deployment: the orchestrator, client nodes 0 and 1, the counter's server (`TopLevelDefs`). -/
def counter_remote_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions] [c0_sem : cmd.client0.Assumptions]
    [c1_sem : cmd.client1.Assumptions] [srv_sem : cmd.server.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σo σ0 σ1 σs : state) (g : GlobalState) (threads : Nat),
    DistDeploy counterAddrs (system σo σ0 σ1 σs) g →
    Robust [] (system σo σ0 σ1 σs) g threads (bound := 2 ^ 63)
```

with, in `Proof/.../counter/TopLevelDefs.lean`, `counterAddrs := ["127.0.0.1:7302",
"127.0.0.1:7303", "127.0.0.1:7301"]` (`ClientAddr0`, `ClientAddr1`, `ServerAddr`) and
`system σo σ0 σ1 σs := [(boot orch, σo), (boot client0, σ0), (boot client1, σ1), (boot server, σs)]`
(echo's `boot`: the command's initializer, then its `main`). Since `Orch` is `remote.Check`, "no
thread has a top-level panic" includes "porcupine accepts the history" under every fault the net
extension allows (cut connections, timeouts, abandoned dials), with unknown-outcome increments.
`bound := 2^63`: lintest's clock (`CounterClock`) needs `receiptBound ≤ 2^63`, as lintest/counter's
`counter_robust`.

**Two changes it needs, outside `remote` (go-ahead asked):**

1. **A ghost-state bundle with non-atomic invariants.** porcupine's linked result takes
   `[NaInvG GF]` (`porcupine/Shared.lean`), and `netGF` (`GooseLang/Ext/Net/Adequacy.lean`) has no
   slot for `NaInvF`; `DistBridge`'s theorems are stated at `netGF`. Proposal: generalize
   `Net/Statement/DistBridge.lean` (`DistBootWp`, `nodeWp_of_distBoot`, `robust_of_distBoot`,
   `robust_of_distProto`) over any `GF` with `[GooseGpreS GF]` (`netGF` its instance, the existing
   callers unchanged by an `abbrev` or explicit `(GF := netGF)`), and define `remoteGF` in remote's
   files: `netGF` with slot 8 `NaInvF` (as lintest/counter's `counterGF`). Alternative: add the slot
   to `netGF` itself (rebuilds every Net example; no statement changes).
2. **The receipt bound in the bridge.** `goose_dist_adequacy` gives the obligation
   `receiptBound GF = N` with `N = n + 1` (`n` the execution's length, `< bound`), and
   `robust_of_distBoot` drops it. Proposal: a variant (additive) whose obligation receives
   `receiptBound GF ≤ bound`, so that the orchestrator's WP can call `Check.spec`.

Both are proved code (no trust added). R4's remaining work after them: the counter's Go model's
`isModel` against `pSeq` (state `(Lo, K)` standing for the configurations), `PendDec`, the codec
(`codecOk`), `opMaybe` of the server's op (from `Counter.Apply`'s logically atomic spec) and of the
client nodes' op (from `Do.spec`), the four `main`s' WPs, the start (`pend_alloc` over the counter's
ghost state), `#print axioms`, `etc/tcb-collections/remote.txt`.

## R4, done (2026-11-22)

The coordinator approved the statement and both bridge changes (2026-11-22). Done:

- **`Net/Statement/DistBridge.lean`** (additive; upamanyus's dsverify-net port, told on #24 by the
  coordinator): `DistBootWpG`, `nodeWp_of_distBootG`, `robust_of_distBootRB`, `robust_of_distProtoRB`: the
  bridge over any bundle `GF` with `GooseGpreS GF`, the obligation given `receiptBound GF ≤ bound`. The
  existing theorems and every Net example are unchanged (`lake build Net` passes: echo, framed,
  acceptloop, duplex, halfclose, preface, shutdown, their `RobustLinked`/`TopLevelRobustness`).
  `remote_start` is now over any bundle; `remote_robustRB` is `remote_robust` over the new bridge.
- **The counter instance** (`Net/Proof|Spec/.../lib/remote/counter/`): `Defs` (`cB`, `cR γs`, `cDec`),
  `Shared` (masks, `syncInv`/`srvTok`, `lin_mono`, `remoteGF`: `netGF` with `NaInvF` at slot 8),
  `ModelDefs` (the pending model: `cSet lo K`, the configurations `(lo + j, K - j pending)`,
  `stepG_pSeq`, `cS`, `cS_pendDec`), proofs of `step`, `Model`, `Codec`, `Gen`, `attempt`,
  `CounterApply` (lintest/counter's `Apply` without the thread token, which the server's `main` has
  none of), `Server`, `Client`, `Orch`, the four `cmd/*/Main.lean`, `Linked.lean`, `TopLevelDefs`,
  `TopLevelRobustness`.
- **The server and the store's state.** `R.sysState` must be fixed at the start (the addresses'
  protocols name it), but the counter's ghost state is made by `New` at run time on the server. So the
  store's state is half of a ghost variable `γs` made at the start, and the server keeps it equal to the
  counter's in an invariant (`syncInv`, at `syncN`, the store's `Eop`).
- **`counter_remote_robust`**: `#print axioms` lists `propext`, `Classical.choice`, `Quot.sound` only.
- `etc/tcb-collections/remote-counter.txt` (roots `^Net/Proof/.../lib/remote/`), baseline empty (as
  `#print axioms` shows). `etc/tcb-report.py --check --update` needs the whole repository built
  (`check_built` checks every root module, ~20k modules), which this worktree is not; to run at landing.

## The read form (2026-11-22, branch `etcd-dist`)

The far side may fire a read's update more than once (etcd's `read_ok_au`), so `opMaybe` hands it
`slotUpd R i Φ`: a write's one-shot `lin`, a read's `□ lin`. Node 0 commits a read at the first firing
whose output's bytes are the answered reply's, which a second prophecy in `Do` gives (the reply's length,
then its bytes, `ResolveU64` each). `Run`/`Check` take the premise that distinct outputs have distinct
bytes. Decision and reasons: `notes/specs-only/ledger.md`, 2026-11-22, "`remote.opMaybe`'s read form";
the details: `notes/etcd-dist-plan.md` §2, "Stage D8".

## `ServeClient`'s one-shot `newClient` and call budgets (2026-11-23, branch `remote-serveclient`)

Two changes to `ServeClient.spec` (claim #28; agreed by Upamanyu on #24, approved by the user), for kits
whose client machine keeps exclusive per-client state (VR's request numbers and ghost state):

- **`newClient` is one-shot.** `ServeClient` calls it once, so its premise is no longer a persistent
  triple `{{ True }} newClient(c) {{ sys, tok sys }}` but the caller's WP, used once:
  `∀ Φ, ▷ (∀ sys, tok sys -∗ Φ #sys) -∗ WP newClient(c) {{ Φ }}`. It may consume exclusive resources to
  make `tok sys`. A kit that proved the triple discharges it the same way, without the `□`
  (`iintro %Φ HΦ` for `iintro !> %Φ - HΦ`).
- **Call budgets** (`Defs.lean`, "Call budgets"). `RemoteGS` gains `bud : GoString → Option Nat` (the node
  at `a` serves at most `N` calls when `bud a = some N`; `none`, unbounded) and `budTok` (the units'
  ghost names). A unit `budUnit a` is the token of a call number `k < N`, exclusive. The request protocol
  carries one per call: `reqP S a` (the address is now a parameter; `svcAddr S a := addrProto a (reqP S a)
  (repP S)`), whose slot holds the unit with the update until the acceptor claims both (`slot_register`,
  `slot_claim`), and the far side's operation gets it with the update: `svcOp S a tok op`,
  `opMaybe R a tok op` (precondition `tok sys ∗ upd ∗ budUnit a`). The far side counts with
  `budUsed a n` (`budUsed_zero`, free) and `budUsed_add : budUsed a n -∗ budUnit a -∗ budUsed a (n+1) ∗
  ⌜∀ N, bud a = some N → n + 1 ≤ N⌝`. The units are made only at the start, by `mapCtx_alloc E addrs N hnd`
  (also `remote_start`/`remote_robust(RB)`'s new `baddrs N hnd`): `N` of them for each of the distinct
  addresses `addrs`, none for the others. The orchestrator spends them: `attempt`/`Report` take one, `Do`
  `readTries` (= `ReadTries`, a read's attempts), and `Run`/`Check` take `nb ≥ ops * readTries` of each
  client address's (`∀ nb, sint.nat ops * readTries ≤ nb → … [∗list] a ∈ addrL, budUnits a nb`), handed to
  `perclient.Run` as a per-call resource (`applySpecId … P f`: each call `apply(id, ·)` gets `P id`; each
  client starts with `calls (P id) ops`). So a client node serves at most `ops * ReadTries` calls (a read's
  retries are calls). No Go change: the budget is ghost state.
- Kits: `mapCtx_alloc ⊤ clientAddrs (ops * 3) (by decide)`, the orchestrator's share and `Orch.spec` get
  the client addresses' units, `addrs_set_proto … (fun a => reqP S a)`, `opMaybe`'s precondition gains
  `budUnit a` (dropped by a kit that does not count). The counter's server address is unbudgeted
  (`bud = none`), so its client nodes' `Do`s get free units (`budUnits_none`).
