# Clients on machines of their own: porting dsverify-lab's `Remote` (plan, R0)

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

Status: **R0, the plan. No code yet.** Questions for the coordinator are in §8.

## 1. The lab's pieces, mapped to ours

| Lab (dsverify-lab `master`) | Here | How |
|---|---|---|
| `harness/remote/remote.go`: `Call`, `Serve`, `ServeClient`, `RunRemote`, the wire, `Codec`, `String` | `examples/lib/remote/remote.go` | **ported, changed** (§3): calls are retried until they get a reply, and replies are cached for duplicate requests. Ops are numbered by a sequence counter on node 0. Frames use kvnet's format. There is no `configure`/`New`, `Start` or `waitMs` |
| `harness/driver` (`driver.Run`: client goroutines, `Gen`, `Start`, the recorder) | `examples/lib/lintest` (proved: `Run` never returns `Illegal` if `apply` is logically atomic) | **reused**. `apply` needs to know the calling client: Q1 |
| `Recorder.lean`, `RunInv.lean`, `ClientSpec.lean` (`opAwpMaybe`, `DriverClientSpec`), `Driver.lean` | lintest's `Defs`/`InvLemmas`/`RunLemmas` (`applySpec`, `genSpec`, `clockSpec`, `linInv`) | **reused**. `opAwpMaybe` (an operation may return an unknown outcome) is dropped: lintest's `apply` always returns an output, and a library folds failure into its model (txnlin's `Output{Err: true}`) |
| `CheckerSpec.lean`, `PorcupineLin.lean`, the porcupine **axiom** | `Proof/github_com/anishathalye/porcupine/` (verified, no axiom) through lintest | **dropped**: our proof replaces it |
| `Remote/RunP.lean`, `DriverP.lean` (copies of the driver's proof with persistent commit postconditions only) | none | **dropped**. We prove lintest's full `applySpec` (any postcondition Φ): the committed continuation goes back to node 0 through the slot invariant, not through the reply (§4) |
| `Remote.lean`: `slotReg`, `reqProto`, `repProto`, `RemoteNames` (per-(c, j) claim tokens and saved predicates, allocated at the start for `j < k`) | `Remote/Defs.lean` | **ported, redesigned** (§4): slots are allocated by node 0 at call time and named by a global map from seq numbers. Each client node holds a frontier, not k claim tokens. No `k` |
| `Remote/Wire.lean` (`le64`, `encRequest`, `encReply`, parsing lemmas) | `Remote/Wire.lean` | **ported** to the frame format, plus prefix lemmas (our reader's facts are about prefixes, §2) |
| `Remote/Call.lean`, `Serve.lean`, `RunRemote.lean`, `Init.lean` | `Remote/{Call,Serve,ServeClient,Run,Init}.lean` | **ported, re-proved** over the net extension's canonical specs (`Net/Spec/net/`) and the protocol library `GooseLang/Ext/Net/Proto.lean` (`dial_au`, `accept_au`, `writeP`/`write_acc`, `read_au`, `close_au`, `deadline_au`) |
| `Remote/Codec.lean`, `CodecKV/CasReg/KVScan.lean`, `KV.lean`, ... (per-model codecs) | `Remote/Codec.lean` (`CodecSpec`) + one codec per instance | **ported in form**: R4 gets one codec. The lab's KV/CasReg/KVScan codecs are not ported (their models are the lab's, not ours) |
| `Remote/Start.lean` (`remote_start`), `Dist.lean` (`remoteDistSafe` over `SafeDist`), `DistSha.lean` | `Remote/Start.lean`, `Remote/Robust.lean` (`remote_robust`) | **re-stated** as `KitDeploy … → Robust [] …` through `robust_of_kitProto` (§6). SHA is not needed |
| `RemoteKit`, `RemoteFacts`, `RemoteMainFacts`, `remoteMainImpl`/`clientNodeImpl` (`rfl` facts about kitgen's generated `Main`) | none | **dropped**. An instance proves its nodes' boot WPs itself, calling `remote.Check`'s and `remote.ServeClient`'s specs. No kitgen |
| `Mux.lean` | not used by `Remote` | not needed |
| kvnet's `kvcheck` (#22) | not edited | **reused as the reference** for the client side: one request frame per connection with a timeout, retries, fresh ids for at-most-once (`checker.fresh`, including its `for {}` at exhaustion). Not imported: `remote` must not depend on kvnet. A kvnet with clients on their own machines would be an instance of `remote` later |

## 2. Semantics: the lab's `NetConn` vs the net extension

| Difference | Lab | Here | What it means for the specs |
|---|---|---|---|
| Errors | codes | kinds `closed \| timeout \| sys`, EOF a read result (`ReadOutcome`) | none. `Call` and `Serve` treat every error the same way (retry, or close and move on), so their specs need no error predicate |
| `Write` | one step | a loop of steps (D15): may write a prefix, then fail | a reader can see a truncated frame. The protocols are prefix-closed (`protoPrefix`, `ProtoPrefixClosed`), and a frame carries its length, so a reader that gets a full frame gets the one that was written (`Wire.lean`: a frame is not a prefix of another one). A truncated frame fails `readFull`, and the reader closes |
| Write lock (D25) | not modeled | a waiting `Write` step may stutter | none: one writer per end |
| Read facts | immediate | one step later (`recvTokL`, `recvTokL_later`) | later credits in the read loop, as `wire.ReadFull`'s proof already does |
| Abandoned dials (D16) | no | `Accept` may return a connection whose dial failed: an empty, shut direction | `Serve` reads EOF and closes. No ghost state was promised for it |
| Deadlines | timeouts | the value is not modeled: any operation may time out once a deadline is set (`deadline_au`) | `Call` retries on timeout, and `Serve` closes. Timing is never used for safety |
| `Listen` | needs an exclusive address token | `addrTok` persistent; `Listen` on an address in use fails with `sys`; the listening token `netLisTok` (v3.4) | `Serve` retries `Listen` in a loop (as the lab's and kvnet's do). The client node's share includes its address's `addrUnset` and protocol |
| Deployment | `cfg.WellFormed`, plan, hosts | `KitDeploy addrs nodes g` (v3.4): addresses distinct and `addrOk`, no connections, no listeners | the instance's addresses are the client nodes' plus the servers' (node 0 listens on none) |
| Crashes | no crash (`SafeDist`) | `Robust crashing stable`. The kits use `Robust []` (`robust_of_kitBoot`) | the orchestrator and client nodes are **stable** (they keep the history). R3 proves the `Robust []` form. Each node's boot WP is a separate lemma, so that etcd-dist's mixed bridge (crashing servers, #22's `NetFs` adequacy) can reuse them unchanged |
| Liveness | not proved | not proved | `Call` retries forever, so a partition between node 0 and client c stalls client c. That is safe: kvcheck does the same |

No change to the net extension or to Perennial is needed. Everything above uses specs and laws that
exist (`Net/Spec/net/{DialTimeout,Listen,Listener__Accept,Conn__Read,Conn__Write,Conn__Close,
Conn__SetDeadline}.lean`, `Proto.lean`, Perennial's `time.Now`, `Time.Add`, `sync/atomic`).

## 3. The Go API (`examples/lib/remote`)

```go
// Codec: a model's inputs and outputs as bytes; Dec* is false on bytes that are not an encoding.
type Codec struct {
	EncIn  func(any) []byte
	DecIn  func([]byte) (any, bool)
	EncOut func(any) []byte
	DecOut func([]byte) (any, bool)
}

// Node 0. lintest's driver: client c's operations are calls to addrs[c]; the history is checked
// by porcupine against model. attempt bounds one try (dial, request, reply).
func Run(model porcupine.Model, addrs []string, codec Codec, gen func(int) any, ops int,
	attempt time.Duration, timeout time.Duration) porcupine.CheckResult
// Check is Run with no timeout; it panics unless porcupine answers Ok (the theorem: it never panics).
func Check(model porcupine.Model, addrs []string, codec Codec, gen func(int) any, ops int,
	attempt time.Duration)

// Client node c: sys := newClient(c), then Serve. Never returns.
func ServeClient(c int, addr string, newClient func(int) any, op func(sys any, in any) any, codec Codec)
func Serve(addr string, sys any, op func(sys any, in any) any, codec Codec)

// The call (exported for reuse and tests): sends request seq with input in until it gets a reply.
func Call(addr string, seq uint64, in []byte, attempt time.Duration) []byte
```

The wire is kvnet's frame format: an 8-byte little-endian length, then the body. One connection
per attempt. The request is the frame `seq ‖ in`, the reply the frame `seq ‖ out`.

- **Node 0** (`Run`): `lintest.RunC` (Q1) with `apply(c, in)`. It takes `seq` from an atomic
  counter (and loops forever at `2^64 - 1`, as kvcheck's `fresh` does), encodes `in`, `Call`s
  `addrs[c]`, and decodes the output. A reply that does not decode is treated as no reply, and
  `Call` retries. The clock is `lintest.CounterClock()`.
- **`Call`**: for each attempt, `DialTimeout`, `SetDeadline(now + attempt)`, write the request,
  read the reply frame. It returns the reply's output if the reply is for `seq`, and otherwise tries
  again. It never returns without a reply.
- **Client node** (`Serve`): `Listen` (retried), then serve one connection at a time. Read a request
  frame (with a deadline). If `seq > last`: decode the input, run `op(sys, in)`, encode the output,
  set `last, cached`, and reply. If `seq == last`: reply `cached` (a retry whose reply was lost). If
  `seq < last`: close (a stale connection). Then close.
- **Too long**: an encoding longer than `MaxLen` (2^20, as kvnet's `maxFrame` bounds a frame) is never
  sent. The orchestrator then waits forever (`for {}`), with no premise and no panic. The R1 tests
  assert the instances' encodings fit (Q4).

**What changed from the lab, and why.**
- *Retry with a reply cache, instead of an unknown outcome.* lintest's `apply` must return an output
  (`applySpec`), and node 0 cannot commit an operation for the client node. The cache makes retries
  at-most-once: the `seq` numbers are increasing for each client node, because client c's goroutine
  is sequential and the counter is atomic. So every operation's output is the one its client
  library's `op` returned. A library with unknown outcomes (an etcd request that times out) returns
  them as model outputs, as txnlin does today.
- *One sequence counter on node 0, not a `j` per client and a `k` per run.* The ghost slots are
  allocated when the call is made, so the start needs no bound on operations.
- *No `configure`/`New`, `Start`, `waitMs`.* etcd-dist's client machines get their endpoints as
  arguments (`client.Main(w, eps)`), and lintest has no start delays.

**etcd-dist's seam** (read on branch `etcd-dist`, `examples/etcd/dist/client/client.go`, a sketch;
not edited). Each workload is `Main(w, eps)` on one machine. With `remote`, a multi-client workload
splits into:

- node 0's `remote.Check(model, clientAddrs, codec, gen, ops, attempt)`;
- client machine c's `remote.ServeClient(c, addr, newClient, op, codec)`.

For `kv`: `newClient(c)` is `clientv3.New` of `eps[c mod k]`, and `op(sys, in)` is
`txnlin.Apply(sys.(*clientv3.Client), in)`. That is `partition.Apply` without the random member,
"each client's operation sequence a function over its own client". `gen` and `model` are
`txnlin.Gen` and `txnlin.Model()`. txnlin needs a codec for its `Input` and `Output` (Go and proof:
etcd-dist's work, sized in §7). Single-client workloads (putget, compact, durable) do not use
`remote`.

The Go module: Q3.

## 4. The proof design (R2)

**Where.** In the part `Net/` (it calls `net`, whose main-tree copy is names-only), as a new goose
project `remote`. Its configuration:

- `local=examples/lib/remote`, `root="Net"`;
- `lean_roots` maps `remote` to `Net`, and lintest and porcupine to the main tree (`=`). Checked: lintest's
  135-module import closure reaches no `net` module, so `Net` can import it;
- specs under `Net/Spec/github_com/.../lib/remote/`, proofs under `Net/Proof/.../lib/remote/`, the
  shared definitions in `Defs.lean`;
- a `Link.lean`, and a collection `etc/tcb-collections/remote.txt`.

**What crosses the network.** Protocols are persistent, so an operation's atomic update moves through
an invariant, as in the lab's spec (R). The differences: slots are made at call time, and the commit's
continuation comes back through the slot.

- The global ghost state (allocated at the start, over `GooseGlobalGS`, as the lab does) has:
  - a map `seq ↦□ γ` (`slotName`), whose authority is in node 0's local invariant with the atomic
    counter;
  - for each client node c, a frontier `mono γc last` (authority at client node c).
- Slot `seq` for client node c, input i, update `AU` and continuation Φ:
  `inv (slotN seq) (pending AU ∨ (monoLb γc seq ∗ (running ∨ done o (K o ∨ takeTok γ))))`.
  - Client node c takes `AU` only by advancing its frontier to `seq`. A slot with `seq > last` is
    therefore still pending, and an update is taken at most once.
  - After `op` returns o, the node stores the committed continuation `K o` as `done o` and keeps
    the persistent fact `doneLb seq o`.
  - Node 0, holding `takeTok`, takes `K o` once the reply arrives.
- `reqProto c cn W`: `W` is a prefix of a request frame `seq ‖ bI i`, with `slotName seq γ`, the slot's
  invariant for c's address, and `□ inOk i`.
- `repProto c cn W`: `W` is a prefix of a reply frame `seq ‖ bO o`, with `doneLb seq o` and `S.ioOk i o`.
  Both protocols are persistent, and so are their facts.
- So node 0's `apply` meets lintest's `applySpec` for **every** Φ. lintest's proof is used unchanged
  (no `RunP` copy, unlike the lab), and so is porcupine's.

**The client node's obligation** (a kit's, or a workload's, for its client library):

- `newClient(c)` gives `is_sys sys` (persistent) and `tok sys` (exclusive, chosen by the node, over
  its own heap: the lab's `client_tok`, without the index `j`, since `Serve` never skips an
  operation);
- `op` meets lintest's `applySpec` shape, lent `tok sys` and the thread's `threadTok`:
  `{{ inOk i ∗ tok sys ∗ threadTok }} <<∀∀ s, libState s>> op sys i @@ Eop
  <<∃∃ s' o, libState s' ∗ ⌜S.M.step s (i, o) = some s'⌝>> {{ RET o'; ⌜equiv⌝ ∗ S.ioOk i o' ∗ tok sys ∗ threadTok }}`.

**The cross-node condition** (as the lab's, made explicit). `libState`, `inOk` and `S.ioOk` are the
same propositions at every node: they are defined over the global ghost state. `CodecSpec` makes
decoding return the value that was encoded (`DecIn (bI i) = i`, `DecOut (bO o) = o`, `bI` and `bO`
injective on admitted values). So the model's inputs and outputs must be heap-free Go values
(scalars, strings, structs of them; not slices, maps or pointers). The counter's `bool`/`int64`
qualify. txnlin's `Input`/`Output` must be checked when etcd-dist writes its codec (its `Output`
keeps its KVs in fixed fields, `NKVs`, which looks heap-free).

**Specs**:

- `remote.Call.spec`: a reply for `seq`, with `doneLb seq o` and its bytes;
- `remote.Serve.spec`, `remote.ServeClient.spec`: never return; safe from the client node's share
  and obligation;
- `remote.Run.spec`, `remote.Check.spec`: lintest's premises (`isModel`, `genSpec`, `libState S.M.init`,
  bounds), `CodecSpec`, node 0's share; then `r ≠ Illegal`, and `Check` returns;
- `CodecSpec`;
- the frame helpers (`writeFrame`, `readFrame`, `readFull`: ported from kvnet's and `wire.ReadFull`'s
  proofs, not imported).

## 5. Stages

1. **R1** Go: `remote.go` and tests over real sockets (loopback). The tests are:
   - an end-to-end run with the counter (§6) on separate listeners, porcupine `Ok`;
   - a fault proxy that cuts connections at every byte offset, drops replies, and delays and duplicates
     requests. Expected: every operation answered once, the history linearizable;
   - a differential check against `lintest.Run` with an in-process counter (same model, same verdicts);
   - stale and duplicate seq handling.

   Also the goose project, `etc/goose.py --check --project remote`, and a gate line in `etc/gates.sh`.
2. **R2**: translation, `Defs`, `Wire`, frame helpers, `Call`, `Serve`/`ServeClient`, `Run`/`Check`,
   `Init`, `Link`. If Q1 goes that way, it also includes lintest's `RunC` and its proof.
3. **R3**: `remote_robust` (§6) with `remote_start` and the per-node boot lemmas.
4. **R4**: the instance (§6), closed, with `#print axioms` and `etc/tcb-collections/remote.txt`.

## 6. The statement (R3) and the instance (R4)

**R3, the generic lemma**, over `KitDeploy` and `KitBridge` as the Net examples (`echo_kit_robust`):

```lean
/-- What an instance proves (the lab's RemoteDistSpec, over the global ghost state). -/
structure RemoteObligations (orch : Expr × state) (clients servers : List (Expr × state))
    (clientAddrs serverAddrs : List GoString) [G : GooseGlobalGS .hasLC netGF] [NetProtoGS] where
  σ : Type; S : ModelSpec netGF σ; libState : σ → IProp netGF; inOk : …; Eop : CoPset
  Γs : Type
  /-- the instance's own start: its servers' shares and the model's initial state, from its servers'
  addresses (the harness sets up the client nodes' addresses itself) -/
  start : ⊢ regCtx -∗ ([∗list] a ∈ serverAddrs, addrUnset a) ={⊤}=∗
    ∃ γ : Γs, libState S.M.init ∗ orchRes γ ∗ ([∗list] c ↦ _ ∈ clients, clientRes γ c) ∗
      [∗list] i ↦ _ ∈ servers, serverRes γ i
  /-- node 0's boot program is safe from its share and the harness's (it calls remote.Check) -/
  orch_boot : ∀ γ ρ, KitBootWp orch.1 (orchRes γ ∗ remoteOrchShare S … clientAddrs ρ ∗ libState S.M.init)
  /-- client node c's boot program is safe from its share and the harness's (it calls ServeClient) -/
  client_boot : ∀ γ ρ c m a, clients[c]? = some m → clientAddrs[c]? = some a →
    KitBootWp m.1 (clientRes γ c ∗ remoteClientShare S … a c ρ)
  server_boot : ∀ γ i m, servers[i]? = some m → KitBootWp m.1 (serverRes γ i)

theorem remote_robust … (H : ∀ [GooseGlobalGS .hasLC netGF] [NetProtoGS], RemoteObligations …) :
    KitDeploy (clientAddrs ++ serverAddrs) (orch :: clients ++ servers) g →
    Robust [] (orch :: clients ++ servers) g threads bound
```

It is proved by `robust_of_kitProto`:

- `remote_start` sets the client addresses' protocols (`addrs_set_proto`), allocates the slot map and
  frontiers, and splits the shares;
- the instance's `start` does the rest.

The orchestrator's and the client nodes' WPs are the instance's own short proofs. Each calls
`remote.Check.wp_proof` or `remote.ServeClient.wp_proof` with its model, codec and client library;
`remote_orch_boot` and `remote_client_boot` lemmas package the common part.

**R4, the instance** (recommended, Q2): a counter on a server node, with two client nodes, so the
state is really shared and the server sits behind the client nodes. Four machines:

- node 0: `remote.Check(counter.Model(), [c0, c1], counterCodec, gen, ops, attempt)`;
- client nodes 0 and 1: `ServeClient` whose `op` is a `remote.Call` to the server;
- the server: `remote.Serve` with `op` = `lintest/counter`'s `Counter.Apply`, which is already proved
  linearizable.

This exercises the library twice. The client nodes' `op` is exactly node 0's `apply` lemma, at one
level down. The cost: `Serve` must deduplicate **per sender** (requests carry a sender id: node 0 is
one sender per client node, and each client node is a sender to the server). That means a `last`
and a cached reply per sender (a small map) and one frontier per (address, sender). It is useful in
general: any server behind `remote` has several senders.

The fallback (R4-min): no server; each client node's `op` is a pure function (model: output =
f(input), state unit). It is cheap, but shows no shared state.

The statement goes in `Net/Spec/.../lib/remote/counter/TopLevelRobustness.lean`:

`counter_remote_robust.spec := ∀ …, KitDeploy counterAddrs (system …) g → Robust [] (system …) g threads bound`

with `#print axioms` (expected: the net extension's and Perennial's, nothing of `remote`), and a
collection `etc/tcb-collections/remote.txt`.

## 7. Sizes

| Piece | Go | Lean (estimate) |
|---|---|---|
| R1 `remote.go`, tests, proxy | ~250 + ~350 | — |
| lintest `RunC` (Q1) | ~20 | ~250 changed/added (`runClient`/`RunLin2` take an id-aware `apply`, `Run` derived) |
| R2 `Defs` (slots, frontiers, protocols), `Wire`, frames | — | ~800 |
| R2 `Call`, `Serve`/`ServeClient` (with per-sender dedup), `Run`/`Check`, `Init`, `Link` | — | ~1600 |
| R3 `remote_start`, boot lemmas, `remote_robust` | — | ~450 |
| R4 counter codec, nodes, server, `TopLevel*`, tcb collection | ~120 | ~900 |
| **total** | ~750 | **~4000** (the lab's `Remote*` is ~5700, of which ~1300 is three codecs) |

For etcd-dist (not this branch): txnlin's codec (Go ~150, proof ~500) and the kv workload's client
node obligation (`op` = `txnlin.Apply`'s existing proof, lent `tok`).

Risks:
- the per-sender map in `Serve` (Goose maps are fine, but they add proof);
- lintest's `applySpec` shape (`threadTok` lent; the masks `Eapp` vs `remoteN`/`lintestN`):
  the slot namespace must be outside `Eop` and `lintestN`;
- the build budget: `Net/` is rebuilt by others too. Use the two build slots only.

## 8. Questions for the coordinator

- **Q1 (lintest's `apply` does not know its client).** `lintest.Run`'s `apply` is `func(any) any`, and
  node 0 must route client c's operation to client node c.
  - (a) Recommended: add `lintest.RunC` whose `apply` is `func(id int, in any) any`. `runClient` passes
    its id, and `Run`/`RunLin`/`RunLin2` call through it with `apply` wrapped. Proof: `applySpec`
    gains an id-indexed variant, and the old one implies it. This edits lintest (Go, translation, ~250
    Lean lines). kvcheck and the other users are unchanged.
  - (b) Leave lintest alone: `remote` wraps `gen` so that inputs carry the client id, and wraps the
    model to unwrap them. That needs a `ModelSpec` for the wrapped model, and porcupine's histories
    show the wrapper.

  May I edit lintest?
- **Q2 (R4's instance).** The counter behind a server node with per-sender deduplication in `Serve`
  (recommended), or R4-min (pure function, no server) first?
- **Q3 (module path, phase 3's export).** `examples/lib/remote` as a Go module of its own,
  `github.com/mit-pdos/etcd-grove/examples/lib/remote` (like lintest; recommended now). The path names
  etcd-grove, so phase 3's leak check will flag it, as it will lintest. Moving both to a neutral path
  (as `models.lab`) is phase 3's change. Or a neutral module path now?
- **Q4 (too-long encodings).** Hang (`for {}`) with no premise (recommended; tests check the instances
  fit), or a premise in `CodecSpec` that admitted values encode within `MaxLen` (the lab's craq/rabia
  bounds)?
- **Q5 (deviation from the lab's spec).** Calls are retried with a reply cache, so there are no unknown
  outcomes at the transport level. The lab kept unknown outcomes (`opAwpMaybe`). With lintest that is
  the only option, but it is a change to the user's design: is it acceptable, or should I ask the user?

## Handoff

(Empty: R0 just written.)
