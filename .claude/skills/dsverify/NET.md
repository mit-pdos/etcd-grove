# The environment: the network, the remote-call library, the statement

Everything here is given and proved (or trusted by the challenge, and then said so in the file's
header). Read the specs' headers before writing anything that calls them: each says what it
assumes and what it gives back.

## The goal's shape

A challenge's statement is an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robustness.Robust`): in every execution of the deployment's machines
of fewer than `bound` steps, with fewer than `threads` live threads per machine, **no thread of any
machine is stuck and none has an unrecovered panic**. A property such as linearizability is not
stated over traces in Lean: it is checked by a program of the deployment that panics otherwise (the
driver's porcupine check, `TESTING.md`), so "no panic" means "porcupine accepts every
history".

```
def <thm>.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions] [client0_sem : cmd.client0.Assumptions] ...  -- one per machine
    [go.BasicIntoValInj],
    (∀ G L, letI := heapAt G L; <premise class> remoteGF) → ...                     -- the premises
    ∀ (σ : Nat → state) (g : GlobalState) (threads : Nat),
    DistDeploy <kit>Addrs (system σ) g →
    Robustness.Robust [] (system σ) g threads (2 ^ 63)
```

- `cmd.<machine>.Assumptions` are Goose's per-package semantic classes (what the translation
  assumes of each program's packages), one per machine; they are not premises you discharge.
- `DistDeploy addrs nodes g` (`Net/Statement/DistDeploy.lean`, trusted): the addresses are distinct
  and valid, the network has no connection, no machine has a listener. Which machine listens where is
  not a premise: the proof shows it.
- `Robust [] ...`: no machine crashes (the empty list is the crashing machines); a process's death
  is a cut connection for its peers.
- The bridge from Iris to `Robust` is given (`Net/Statement/DistBridge.lean`,
  `robust_of_distProtoRB` and its siblings): you prove a start obligation (from the addresses unset,
  allocate the ghost state, give each machine a resource `P i`) and, per machine, its boot program's
  WP from `P i` (its packages' initializers, then `main`).

## The network model (the net extension)

`net` is Goose's translation of Go's `net` over the **net extension**
(`GooseLang/Ext/Net/`, Linux TCP semantics; its specs in `Net/Spec/net/`: `Dial`, `DialTimeout`,
`Listen`, `Listener.Accept`/`Close`, `Conn.Read`/`Write`/`Close`/deadlines, `TCPConn`'s options,
`OpError`'s methods). Its faults are executions, not adversary code: **any dial may fail, any
connection may break at any moment, any read may wait forever or fail, bytes in flight may be lost
when a connection breaks**, and a read after an error returns no more bytes. Timing is not modeled:
every timeout may fire at any moment. So partitions and slow links are already in the theorem's
quantifier; a protocol's correctness may not depend on a message arriving.

The specs are **logically atomic** over the connection's state: a caller of `Conn.Read` supplies an
atomic update over the end's state (`netEnd`, `netDir`) and gets back its result with the bytes. The
address predicates (who may listen at an address, who may dial it, the protocol on its connections)
are ghost state the deployment's start allocates (`NetProtoGS`): a kit gives each address a
protocol (the bytes each side may send) and proves its machines follow it.

## The remote-call library (`examples/lib/remote`)

Clients run on machines of their own: no client shares a process with another, so no proof can rely
on one observer of several clients' steps. The library (Go: `examples/lib/remote/remote.go`; specs:
`Net/Spec/.../examples/lib/remote/`) has:

- `Check` / `Run` (the driver, node 0): lintest's driver with one client per client address,
  each operation a `Do` at that address; the history checked by porcupine against the model, a panic
  unless porcupine answers `Ok`. Its spec's premises are the kit's obligations: the model refines a
  Lean model spec (`isModel S m`, `TESTING.md`), the codec is correct (`codecOk`), the far side's
  store and its pending-writes model (`PendDec`, `pendCtx`, `pendLib`), each address serves the
  service (`remoteAddr`), and the **call budget**: each client address holds `nb ≥ ops * readTries`
  call units (`budUnits`).
- `Do` (one operation at a client machine): a write gets one attempt, a read `ReadTries`; with no
  answer, a write's outcome is unknown (it may have taken effect, may later, or never) and `Do`
  returns the model's unknown output, which the model treats as a pending write. Its spec takes the
  operation's update through a choice made from `Do`'s prophecies.
- `ServeClient` (a client machine's program): makes its own client of the system once (`newClient`,
  a one-shot resource, not a persistent triple), then `Serve`s calls one at a time, each with one
  call unit; it never returns.
- `Serve`: listens, serves each connection's one request to completion, answers on the connection
  that carried it; a cut connection loses the answer and never repeats the operation.

A kit's client machine's job is therefore: from its own client of the system, given one call unit
and an operation's update (an atomic update on the abstract store, to commit at the operation's
linearization point), run the operation and return the output with the update's result. That is
the **client spec of the system** the kit's proof must establish, the place where linearizability
is proved.

## Codecs and models given with the environment

- `models/` (Go module `models.lab`): the codec helpers (`pbcodec`, `jsoncodec`, proved in
  `Net/Proof/models_lab/`) and the generators of a kit's codecs (`models/net/rpc/rpcgen.py`,
  `models/json/jsongen.py`, `models/protobuf/pbgen.py`); a generated codec is checked by its
  generator's `--check`. Each model's evidence is in `models/README.md`.
- `net/rpc`, `net/http`, `bufio`, `encoding/*` and the other standard-library packages the
  environment covers have specs in `Net/Spec/`, `Spec/` or `Dsverify/Proof/<pkg>/`: search before
  writing one (`CHALLENGE.md`, "One canonical spec per function").
