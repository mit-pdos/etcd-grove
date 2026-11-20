# M2: Go's `net` as the bottom layer (design note, 2026-11-12, for review)

Replaces `notes/harness-m2.md` (transports over Perennial's `Net`), which the user superseded the same day.

## The direction (the user, 2026-11-12)

- **Applications use Go's `net` package literally.** No transport is ported onto lab code: hashicorp's
  NetworkTransport, eliben's RPC client and Gryff's per-peer TCP readers and writers stay as they are, and become
  verified code.
- **For the theorems, a model of the `net` package is the spec.** Goose gets a trusted model of a subset of `net`,
  whose semantics is a new Perennial extension: TCP as Go presents it (section 2). Principle 1 of the plan still
  holds ("the fault model is the network's semantics"); only the semantics changes, from datagram sets to
  connections.
- **Network testing happens entirely outside Go.** Nodes run as separate processes in containers, and the tests
  change the networking between the containers (delay, loss, partitions, resets), in the style of Antithesis. The
  theorems do not depend on the test rig: whatever the real network does must be a behavior of the model, which is
  the one review question.
- **The case studies are not modified** (the user, 2026-11-12): we may have to prove more, but the code proved is
  the code as released. Where Goose cannot translate a library the target uses (reflection-based codecs: hashicorp's
  go-msgpack, `net/rpc` and gob; logging, metrics), the library gets a trusted model, as `net` does, rather than
  the target being edited. A change to a target's own code is made only where that code itself uses Go that Goose
  cannot translate, and each such change is recorded as a Goose gap to close.
- **Crashes later, in the same frame:** a crash is a container kill and restart. Perennial's
  `goose_dist_crash_adequacy` already models it: a node restarts with its boot program, the network unchanged. That
  is phase 3.

## What exists to build on

- **Distributed adequacy** at the pinned Perennial (`4c8617a`): `goose_dist_adequacy` (`GooseLang/DistAdequacy.lean`).
  A system is a list of nodes, each with its own threads, heap and local extension state, sharing a global state (a
  network). From a WP for each node's boot program, given the extensions' global start, it concludes that no node
  panics and each node's final value meets its postcondition. `goose_dist_crash_adequacy` adds crashes.
- **Trusted models of standard packages** (`Perennial/TrustedCode/`: `sync`, `time`, `bytes`, `strings`, `strconv`,
  `fmt`, `log`, `errors`, ...). `net` becomes one more. `io`, `bufio` and `encoding/binary` are not there; section 4.
- **Grove's extension** has connections (`Listen`, `Connect`, `Accept`, `Send`, `Receive`), but they are message sets
  with reordering and duplication, not `net.Conn`'s byte streams. It is the template for writing an extension with
  global network state and its adequacy, not the semantics we want.
- **M1's generic lemma** is per node and does not mention the network: the clients, the recorder and the checker run
  in one Go program. It moves unchanged into the client node (section 3).

## 1. The `net` model (trusted)

The subset the targets use:

- `net.Listen("tcp", addr)` and `Listener.Accept`, `Close`, `Addr`.
- `net.Dial("tcp", addr)` and `net.DialTimeout`.
- `Conn.Read`, `Write`, `Close`, `SetDeadline`, `SetReadDeadline`, `SetWriteDeadline`, `LocalAddr`, `RemoteAddr`.
- Errors: `io.EOF`, and `net.Error` with `Timeout()`.

`net.Conn` is an interface, and the model gives it one concrete implementation, whose methods are the extension's
operations. Code that takes a `net.Conn` (hashicorp's `StreamLayer`, `bufio.NewReader(conn)`) goes through Goose's
ordinary interface translation. The Lean side is `TrustedCode/net.lean` plus the extension, about the size of `Net`'s
(its `Impl.lean` and `Specs.lean`), which the user reviews once.

## 2. The semantics: TCP as Go presents it

The global state: the listening addresses, and per connection two byte streams (one per direction), each the bytes
written and not yet read, plus each end's state (open, closed, broken).

- **Listen** succeeds on a free address or fails. **Dial** fails, or makes a connection that the listener's next
  **Accept** returns.
- **Write** appends a prefix of its buffer and returns how much. A short write comes with an error.
- **Read** returns some of the next unread bytes (at least one, at most the buffer), in order. It waits while there
  are none, and returns `io.EOF` once the peer has closed and every byte is read.
- **A break may happen at any operation:** the connection becomes broken, an arbitrary suffix of the bytes in flight
  is lost, and every later operation on either end returns an error. This is how a reset, a long partition or a
  keepalive failure shows up at `net.Conn`.
- **Loss on the wire is not a behavior of its own.** TCP retransmits, so at `net.Conn` it is only a delay or, in the
  end, a break.
- **Deadlines:** with a deadline set, any Read or Write may return a timeout error instead, a Write possibly after
  writing a prefix. The connection stays usable, as in Go.
- **Nothing is reordered, duplicated or corrupted** within a connection.

Breaks and timeouts are nondeterministic choices at the operations. Since only operations observe the network,
that covers "at any time". Real networks fit: what tc, iptables or a container restart can do to a TCP connection is
a delay, a reset or a stall, each a behavior above.

**Specs** (proved once, from the semantics): ownership of each end's stream as ghost byte sequences. The writer owns
`written γ c bs`; the reader owns `consumed γ c n`, and each read hands over the next bytes as a persistent prefix
fact. Breaks and timeouts appear as error results that keep the ghost state consistent. A predicate on byte
offsets carries the protocol's meaning (the analogue of the M2 note's `Φ`, over bytes instead of messages), so
framing and decoding proofs build on it (section 4).

## 3. The theorem's shape

- **Nodes:** server nodes 1..n run the kit's server program (the target's node `main`, with its id, address and
  peers' addresses as constants or arguments); node 0 is the **client node**, M1's `Main`: the clients, the recorder,
  the checker, talking to the servers over `net`.
- **The statement:** `SafeDist`, a lab definition over `goose_dist_adequacy`: for the node programs and the
  addresses, no node panics. The extension's start premise: no listeners, no connections. A new bridge,
  `safeDist_of_wp`, replaces `safeNet_of_wp` and splits the start resources across the nodes (each server's listen
  address goes to its node).
- **The run's goal** keeps M1's two parts: the client operations' `atomic_wp` specs, now over the connections to the
  servers, and `SafeDist` derived through the generic lemma at node 0. The run also proves the server nodes' boot
  WPs, from the invariants its client spec uses.
- **What the test checks** is what the theorem covers: the client node's linearizability check, so any failure in a
  test is a counterexample to the theorem.

## 4. Above `net.Conn`: framing and library models

- **Framing helpers, proved once:** `io.ReadFull`, `bufio.Reader`/`Writer` (the subset the targets use), and
  `encoding/binary`'s fixed-width integers. Either translated from Go's own sources, where Goose can, or modeled. They
  carry the byte-offset specs of section 2 up to "the next frame is the k-th one written".
- **Codecs, as trusted models** (no change to the targets):
  - **Gryff** marshals by hand (fastrpc) over `bufio`: translated and proved, nothing trusted.
  - **hashicorp/raft** encodes with go-msgpack, by reflection. A model of the encoder and decoder on a
    connection: what the decoder returns is the value the peer's encoder wrote, for the target's message types
    (the RPC structs, log entries, configurations). Its tests: random values of those types round-trip through the
    real library.
  - **eliben/raft** uses `net/rpc` with gob. A model of `net/rpc`: `Call` runs the registered method at most once on
    the request the caller passed and returns its reply, or an error; gob as hashicorp's codec model.
- **The codec models are keyed on the target's Go types, fixed by the model, never a parameter a proof chooses.**
  etcd-grove's lesson (`/shared/etcd-grove/notes/pbenc-ok-inconsistent.md`, `notes/grpc-msg-models.md`): its protobuf
  and grpc message axioms quantified over a caller-built record of a type's wire model, so a record whose `recv`
  is `False` proved closed `False`, and 17 safety results were vacuous until the models were keyed on registered
  types. Each of our codec models gets the same attack before use (section 5).

## 5. Borrowed from etcd-grove (`/shared/etcd-grove`)

**In the long run etcd-grove's tests move to this plan too** (the user, 2026-11-12). So the `net` extension, the
`net` model and the rig are built to be adopted there: etcd-grove's conventions where they do not conflict with ours,
the extension independent of the harness's other modules, and the rig independent of any kit (any node binaries,
from a config file). Borrowing from etcd-grove is encouraged.


etcd-grove proves etcd (Raft, the server, the cache, clientv3, k8s's use of it) with trusted models of grpc and
protobuf, and its own GooseLang extensions. Its trust boundary is grpc's API (`Server.Serve`, `ClientConn.Invoke`,
streams), not `net`. That fits etcd, which uses grpc; our targets use `net` directly. What we take:

- **Trusted models as `TrustedCode/<pkg>.lean`**, listed as `trusted` in the package's Goose configuration, each with
  a docstring saying why it is faithful (citing the Go source by file and line). Model code with bodies is proved
  over; its leaves are **model-only names** (`pkg#model.X`, which no Go function can have), axiomatized, each
  docstring naming the Go composite it stands for (`TrustedCode/google_golang_org/grpc.lean`).
- **Extensions as `GooseLang/Ext/<Name>/{Impl,Specs}.lean`**, the extension's name being the Go package it
  implements, and the package's models calling it by name (`ExternalOp E.name "Read"`).
- **A semantics-examples package per extension:** every decision of the trusted semantics has a Go example with the
  decision, the Lean names, the outcome allowed or excluded, and the evidence (measured, documented with a
  citation, or assumed); a change to the semantics updates its example in the same commit (their Linux file
  extension: `examples/osfs/semantics/`). For `net`: partial writes, a break losing a suffix, reads after a peer's
  close, deadlines leaving the connection usable, each demonstrated on the rig.
- **One claimed configuration:** an extension of an OS interface claims one target configuration and nothing wider
  (theirs: Linux 7.0, ext4 defaults, `notes/axiom-review/fs-config/`), and every claim is tested on it. Ours: Linux's
  TCP over the rig's veth links, Go 1.27's `net`.
- **Streams as two FIFO queues with mono-list ghost state** (their gRPC stream spec,
  `notes/grpc-stream-spec.md`, after Perennial's SPSC channel idiom): the shape of section 2's specs, with breaks
  added (their streams are reliable until the call ends).
- **Axiom sweeps and attacks:** every trusted model is attacked before use (try to derive `False`, try to prove a
  program safe that panics in Go: `examples/axiomcx`), and the gates track which results rest on which axioms
  (`.lake/tcb.json`, `etc/tcb-baseline.txt`).
- **Directly reusable** if a target speaks grpc (etcd itself, or a later case study): their grpc and protobuf models
  and specs.

## 6. Tests outside Go

**`Main` has no adversary** (the user, 2026-11-12). The theorem covers every behavior the `net` model allows (any
break, partial read or write, deadline, at any point), so a thread in the test program that disconnects or delays
the network would add nothing to it, unlike the standalone kits, whose adversary is what puts faults in scope. The
test program is the client node's workload and its history check, nothing else. The tests are for coverage
(kits/README 4a) and for a sanity check before a run: a fault-free run reaches the normal paths; the rig's faults
below, applied from outside the processes, are optional and reach the error paths (reconnects, timeouts) for the
coverage report only. They change neither the program nor the theorem.


- **The rig:** each node a process in its own network namespace (containers, or plain `ip netns`) on one machine,
  joined by veth links. Faults come from `tc netem` (delay, jitter, loss: TCP turns loss into delay), `iptables` DROP
  (partitions and asymmetric partitions: stalls, then breaks at timeouts) and REJECT with `tcp-reset` (immediate
  breaks), applied and lifted on a schedule. Crash and restart (kill the process, restart it with its arguments) is
  phase 3.
- **The client node** runs M1's `Main` and checks the history. The rig records the fault schedule, so a failing run
  can be replayed approximately (not deterministically; deterministic replay is Antithesis' hypervisor, which we do
  not have).
- **Coverage:** each process built with `-cover`, `GOCOVERDIR` per container, profiles merged; reported per kit as
  kits/README 4a says for harness kits.
- **It replaces** M3's in-process scheduler and netsim (in M3's place in the plan).

## 7. Steps

| step | what | done when | who |
|---|---|---|---|
| M2a | the extension (semantics, Lean), `TrustedCode/net.lean`, the `SafeDist` statement and its start premise | they typecheck; you review the semantics | lab, with a subagent for the Lean |
| M2b | the extension's ghost state and specs, its instance of distributed adequacy, `safeDist_of_wp` | proved, no `sorry` | subagent |
| M2c | a probe: an echo server node and a client node using `net` literally, translated by Goose and proved through `SafeDist` | end to end, no `sorry` | subagent |
| M2d | the framing helpers (`io.ReadFull`, `bufio`, `encoding/binary`) with specs | proved | subagent |
| M2e | the rig (namespaces, faults on a schedule, coverage) on the probe and on a toy replicated register | runs, faults happen, coverage reported | subagent |
| M2f | library models: go-msgpack's encoder and decoder (hashicorp), `net/rpc` with gob (eliben), each keyed on the target's types, with round-trip tests against the real library and an attack (section 5) | models stated, tested, attacked | subagents |

M2a first, for the review of the semantics. M2e can start beside M2a, since the rig does not depend on the proofs.

## Effects on the plan

- **M0 and M1 stand.** paxos-m0 and paxos-m1 remain the record of the `Net` version, and the generic lemma moves into
  the client node.
- **The mux and netsim are retired for new kits.** xiang90/paxos, whose code wants datagrams, would get a small
  message layer over connections if it is used again.
- **M3** becomes the rig (section 6) plus the harness's own tests.
- **M4's pilot is xiang90/paxos ported to `net`** (the user, 2026-11-12: paxos is our own test case, so porting it
  is fine; the rule against modifying case studies is for the systems we report on). Its agents talk through Go
  channels behind an unexported `network` interface; the port implements that interface over `net.Conn` (a
  connection per pair of agents, length-prefixed frames, hand-written marshaling as in M0, `encoding/binary`), with
  acceptors and learners as server nodes and the client node running `Main`. No library model is needed. Kit prep
  starts beside M2b, once the semantics is reviewed; the run launches after M2c (the echo probe proved end to end),
  M2d (framing helpers) and M2e (the rig, for the kit's tests). It has baselines: five earlier Paxos runs and
  paxos-m0-1 over `Net`. After it: go-vsr (raw `net`, models of `encoding/json` and `log/slog`), then eliben/raft
  (`net/rpc` and gob) and Gryff, unmodified.

## Decisions to make (recommendations first)

1. **One client node running M1's `Main`** (clients, recorder, checker in one process): the generic lemma unchanged.
   The alternative is clients spread over nodes, with an offline checker outside the theorem.
2. **Configuration as constants per node** (id, own address, peers' addresses) in each node's `main`, generated by
   the kit; the statement lists the addresses.
3. **Breaks and timeouts as choices at operations** (section 2), not as separate steps.
4. **The rig on network namespaces** on one machine (fk-lean1 or fk-lean2), not full containers, unless a target
   needs its own file system before phase 3.
5. **The framing helpers translated from Go's sources where Goose can**, modeled otherwise.
6. **The M4 pilot:** xiang90/paxos ported to `net` (decided with the user). go-vsr next.

## The Paxos pilot's result (paxos-m2-1, 2026-11-13)

The first kit on the `net` model ran on fk-lean2 and is verified (`final` 523cdb7; README row; `theorems/paxos-m2-1`).

- **Effort.** 82 active minutes and 224M tokens (0.92M output), against paxos-m0-1's 196 minutes and 191M (0.82M)
  over Perennial's datagram `Net`. Proof: 8,254 lines against 5,354. The model is richer (streams that break
  mid-frame, partial writes, deadlines, six separate nodes), yet the run took less than half the wall time. It
  froze its interface early and then had eight agents prove one package each.
- **Trust.** Nothing beyond the kit's: Lean's three axioms, Goose's names-only declarations (`net`, porcupine,
  `sync.Map`, synctest) and `time.Now`. 265 axioms in all.
- **Bugs and fixes.** None. The fork gained only a test (`stress_test.go`: an in-process deployment through proxies
  that cut and truncate connections). So the kit's rig coverage stands: 86.6% fault-free, 87.8% with faults.
- **Proof structure worth reusing.** The Paxos invariant is an append-only ghost log of protocol events, and agreement
  is proved by induction on log position, not ballots: time isn't modeled, so ballots may wrap. The B form's error
  case forces helping: the deciding acceptor vote commits the update of a client whose value was decided. The
  transport lemma: a complete frame read from a stream that may end mid-frame is a frame the sender wrote.
- **Spec feedback** (the run's `notes/spec-feedback.md`). For the kits and the harness:
  1. `DistSpec`'s start resources are elaborated with only `GooseGlobalGS`, so the shared invariant and the
     protocols must be stated over the global ghost state. The kit should say so (it cost a review round).
  2. `client_tok` was `True` here; document it as optional.
  3. The B form is the right strength.
  4. The statement says nothing about servers' state no client observes (two learners agreeing). Proved internally
     but not exported; a server-side observable would be a statement change.
  5. List `time.Now`'s axiom with the net model in ISSUES.md.
- **Lab tooling.** The first verify failed on two lab-side problems, both fixed (`verify.sh`'s root modules; `test1`'s
  stale marshal zip). Any throwaway run's module cache must be cleared when the lab cache is scrubbed.
