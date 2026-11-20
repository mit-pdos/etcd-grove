# grpc-model: a lab model of gRPC's unary API and protobuf over Go's net (2026-11-14)

A harness piece, made for QuePaxa (`dedis/quepaxa` at `bd16e25`) and meant to serve later, larger
grpc-based targets. QuePaxa's replicas talk to each other through grpc: three unary methods of one
service, `Consensus` (ESP, FetchBatches, InformDecision). Its clients talk to the replicas over
plain TCP, using `proto.Marshal`/`Unmarshal` of `proto/client`'s messages through
`clientwrapper.go`; `client/` and `proto/client` do not use grpc. The kit itself is a later step.

The precedent is net/rpc and gob (`notes/craq-net.md` decision 2) and encoding/json
(`notes/vsr-net.md`):
- the library is a Go model, translated by Goose in place of the real module and proved once in
  the harness over the net model;
- reflection is replaced by a codec that kitgen generates per kit, keyed on the kit's types and
  tested against the real library.

Shapes were borrowed from etcd-grove (`/shared/etcd-grove`: `TrustedCode/google_golang_org/grpc.lean`,
`notes/grpc-msg-models.md`, `notes/grpc-stream-spec.md`, `notes/pbenc-ok-inconsistent.md`): unary Invoke and handler
specs over bytes, status errors, and the per-type lesson. Its `pbEnc_ok` and `ProtoMsg` axioms
were quantified over a caller-built record of a type's wire model, and a record with `recv` set to
`False` proved closed `False`. Here no wire-model axiom exists. The codec's predicate transformers
(`PbCodec`) are a class whose instance the run chooses and must prove its generated Go functions
meet (`kitCodecOk`); the final statement (`SafeDist`) does not mention them. What is trusted is
that the generated Go codec behaves like real protobuf, and that is tested, not axiomatized.

## What was built

### Go models

**`harness/rpcmodel/grpc`** is module `google.golang.org/grpc` (v1.84.0's API), the unary subset. Files:
- `wire.go`: the wire format and the package doc, which states the trusted claim.
- `clientconn.go`, `server.go`, `options.go`.
- `codes/`, `status/`, `credentials/`, `credentials/insecure/`.

**`harness/rpcmodel/protobuf`** is module `google.golang.org/protobuf`:
- `proto/proto.go` has `Marshal` and `Unmarshal` over the kit's codec, plus lab-only `SetCodec`,
  `MarshalValue` and `UnmarshalValue`.
- `reflect/protoreflect` and `runtime/protoimpl` are names-only stand-ins. They hold just enough
  for protoc-gen-go's generated `.pb.go` to compile unmodified against the model. This was checked
  with protoc-gen-go v1.27.1 output (QuePaxa's) and v1.36.12 output (the difftest's).

**Substitution.** The real modules are used outside the model build (they are in the offline
module cache: grpc v1.84.0, protobuf v1.36.12). The model build and Goose use a modfile
(`go.model.mod`), which is `go.mod` plus `replace google.golang.org/grpc => …/rpcmodel/grpc` and
`replace google.golang.org/protobuf => …/rpcmodel/protobuf`, with tag `rpcmodel`. Goose's loader
honors `GOFLAGS=-modfile=…` (checked on QuePaxa). This differs from net/rpc's GOROOT substitution
because these are modules, not std. It also differs from uuid/gods, which are replaced in both
builds because the real modules are not cached.

### Codec generator

`harness/kitgen/pbgen.py` handles kit.toml `[protobuf]`, and `harness/pbcodec` holds the wire
helpers: varints, tags, skipping, and UTF-8 validation.

The section looks like this:
```toml
[protobuf]
imports = { raxos = "raxos/replica/src" }
enums = []
[protobuf.messages]
"raxos.ProposerMessage" = [["Sender", 1, "int64"], ["P", 3, "raxos.ProposerMessage_Proposal"], ...]
```
- A listed message `T` used as a field kind means `*T`, and `[]K` means repeated.
- Supported: proto3 implicit presence; int32/64, uint32/64, sint32/64, fixed32/64, sfixed32/64,
  bool, string, bytes, enums, messages, and repeated forms (packed).
- Refused with a clear error: oneofs, maps, optional, float/double, groups, proto2.
- `pbgen.py --from-pb FILE.pb.go` drafts the section from the generated struct tags.

Generated files, in the kit's adapter package:
- `pb_gen.go`: `pbMarshal` and `pbUnmarshal`, a type switch over the listed `*T`; Goose-translatable.
- `pb_model_gen.go`: `registerProto`, which calls `proto.SetCodec` under tags rpcmodel or goose.
- `pb_real_gen.go`: a no-op.
- `pb_gen_test.go`: tests against the real protobuf, described under "Testing" below.

kitgen wires the section in: the files, the `PbKit` instance in the statement, and the audit
lines.

### Lean (`harness/lean/Harness/Proof/grpc/`)

| file | contents |
|---|---|
| `Base` | `isPkgInit` of the 8 translated packages (proto's codec registry as net/rpc's) |
| `initialize` | their initializers |
| `Pb` | `SetCodec`, `getCodec`, `Marshal`, `Unmarshal`, `MarshalValue`, `UnmarshalValue` over `PbCodec` |
| `Proto` | wire format, world, connection invariant, protocols |
| `Wire` | framing: net/rpc's proofs adapted; payloads gain a tag |
| `StatusSpec`, `Status` | status and codes |
| `ServerDefs` | `handlerOk`, `decOk`, `svcOk`, `isServer`, `NewServer`, `RegisterService` |
| `ServerGhost`, `Server` | the server loop |
| `ClientDefs`, `ClientGhost`, `Client`, `Setup` | the client and the world set-up |

Proof status is in "Results".

## Decisions

1. **Wire format: the model's own, not HTTP/2.** Every node of a theorem runs the model.
   - Frames are net/rpc's: an 8-byte little-endian length, then the payload.
   - A payload is `tag ++ seq ++ len(s) ++ s ++ body`, each number 8 bytes LE.
   - The client sends calls (tag 0, seq, "/svc/method", request) and cancellations (tag 1, the seq
     given up).
   - The server sends answers (tag = status code, seq, status message, reply).
   - A call's seq is its frame's number among the client's frames on the connection. Seqs are
     never reused on a connection; a connection that reaches 2^64-1 frames shuts down. So a
     response names its call directly, which keeps the client proof simpler than net/rpc's (no
     wrap-around bookkeeping).
   - A model node cannot talk to a real grpc node. The theorem never needs it, and the rig runs
     every node in the same mode.

2. **At most one run per Invoke.** grpc-go never runs a unary handler twice for one Invoke:
   - Transparent retry resends only streams no server application received (REFUSED_STREAM, or a
     GOAWAY above the last stream processed).
   - Retry policies and hedging are off without a service config.
   - The model makes one attempt on one connection.
   - A real transparent retry that then succeeds is covered: in the model, the first connection
     breaks and the call goes out on a fresh one.

3. **Reconnection.** `Dial`/`NewClient` do not connect (the real non-blocking dial). The first
   call dials, and so does the next call after the connection broke. There is no backoff, so the
   model may redial at once where real grpc waits; that is timing only. A dial failure gives
   `Unavailable`. With `WaitForReady`, a real call waits where the model's fails fast; the model
   then has extra failures, which is sound for safety. `WithBlock` is accepted and ignored.

4. **Contexts and time.** Time is not modeled, so a deadline may expire at any moment, as with the
   net model's deadlines.
   - Invoke selects on its call's answer and on `ctx.Done()`, through Perennial's translated and
     proved `context` (`isContext`, `isContextDone_receive`). A done context returns
     `DeadlineExceeded` or `Canceled` with Go's messages.
   - When a call is abandoned, the client sends a cancellation frame, as the real client resets
     the stream.
   - The server gives each call `context.WithCancel(context.Background())`. It is canceled when
     the handler returns, when the client's cancellation arrives, and when the connection ends;
     the real stream context is canceled on the same three events.
   - Not modeled: a handler's `ctx.Deadline()` is always unset (the real one carries the client's
     deadline), and metadata and peer info.

5. **Status codes and messages.**
   - The handler's own status passes through; a non-status error becomes Unknown with its
     `Error()`; context errors become DeadlineExceeded/Canceled; an unknown service or method
     gives Unimplemented with real grpc's text.
   - A request or reply the codec cannot handle gives Internal. Size limits as the real defaults:
     4 MiB received, 2^31-1 sent; over them, ResourceExhausted.
   - A broken or refused connection gives Unavailable. After `Close`, Canceled.
   - A nil message (not a typed nil) encodes as the empty message, as real grpc's `encode` does.
   - Only codes are claimed in general. The messages of handler statuses, unknown methods and
     context errors are claimed too; other messages are the model's own.
   - `status.FromError`/`Code` recognize only the model's own status errors, by dynamic type.
     The real ones also accept any type with `GRPCStatus()`, and wrapped errors.

6. **Dispatch is the target's own code.** The generated `_X_Handler` functions and `ServiceDesc`
   (`*_grpc.pb.go`) are plain Go. Goose translates them and the run proves them (`handlerOk`), so
   no dispatch table is trusted.
   - The real `RegisterService` checks by reflection that the implementation satisfies
     `HandlerType`. The generated `RegisterXServer(s, srv XServer)` can only pass one that does,
     so the model skips the check.
   - Registration after Serve, and a duplicate service, are real `Fatalf`s; the model panics. The
     spec rules both out with an owner token that `Serve` takes.
   - A descriptor with streams makes the model panic: streams are outside the subset.

7. **Serve and Accept errors.** The net model's Accept failures have an arbitrary `Temporary()`
   that its specs do not expose. Real `Serve` retries a temporary error and returns any other.
   After an Accept error, the model therefore chooses either way with `primitive.RandomUint64()`
   (random when run, arbitrary in Goose), which covers the real behavior. Consequence for
   QuePaxa, whose `Serve` error path panics: under the net model a non-temporary Accept failure is
   always possible, so that panic is reachable. The kit must face this (see "What the QuePaxa kit
   still needs").

8. **Protobuf codec semantics.** Each point was checked against v1.36.12, by reading its code or
   running it.
   - Encoding is byte-exact: field-number order, proto3 defaults omitted, a non-nil empty nested
     message written, a nil element of a repeated message written as an empty message, a typed
     nil marshaling to `nil, nil`.
   - Unmarshal resets, then merges: scalars last-wins, messages merged, repeated appended, packed
     and unpacked both accepted.
   - Unknown fields are validated and dropped (the real code keeps them; no model node writes
     any).
   - Errors (not their messages) are where the real ones are: malformed input, invalid UTF-8 in
     strings both ways, nesting over 10000.
   - Unmarshal into a nil pointer panics, as the real one does.
   - `String()`, `Reset()`'s reflective part, `ProtoReflect`, `Descriptor` and the file's
     descriptor init are outside the subset: names only for Goose.

9. **The generated `.pb.go` for Goose.** These are the kit's per-package goose configs, and the
   QuePaxa scratch check verified that they work:
   - `translate = ["*", "!*.Reset", "!*.String", "!*.ProtoReflect", "!*.Descriptor", "!F_*",
     "!File_*", "!init.0"]`;
   - `trusted = ["init.0", "File_*", the F_* variables]`, with trusted no-op Lean bodies in the
     style of `TrustedCode/os.lean`.
   - Pitfall: a trusted name must also be excluded from `translate`, or it is translated.
   - Trusted: the file's descriptor registration does nothing that a reflection-free program can
     observe.
   - The `*_grpc.pb.go` files need nothing excluded.

## What the theorem trusts (beyond the net model)

**The two Go models.** The claim is the package docs' semantics (decisions 1-7). It is tested,
not proved, by `harness/rpcmodel/grpcdifftest/run.sh`: the same tests against the real modules
and the models.
- `grpc_test.go` covers calls, concurrency (200 calls on one conn), every error path, deadlines
  and cancellation, with the handler's context observed done, reconnection after cuts by a proxy,
  a cut while waiting, size limits, Close, Serve's return, and the status/codes package.
- `example/` holds the two-node example described under "Testing".

**Each kit's codec.** It is generated, its listed fields are on the audit list, and it is tested
against real protobuf (described under "Testing").

**The pbcodec helpers.** Translated; tested against protowire and unicode/utf8.

**Per kit, the `.pb.go` files' trusted no-op init** (decision 9).

**Axioms.** The proved specs use the net model's axioms (216 for net/rpc's `Client.Call.wp`, the
probe) plus 6 Goose names-only type declarations of Perennial's `fmt` (`fmt.pp`, `fmt.readRune`
and their underlying/zero_val). `status` imports `fmt` for `Errorf`/`Newf`, which protoc-gen-go
v1.2x's `Unimplemented*` methods call. These are type names, not semantic claims, the same any
program importing Perennial's fmt gets. No new axiom.

| theorem | axioms |
|---|---|
| net/rpc `Client.Call.wp` (baseline) | 216 |
| `grpc.initialize'`, `readFrame`, `NewServer`, `RegisterService` | 222 |
| `status.FromError` | 18 |
| `proto.Marshal` | 12 |

## Testing

All of the following pass with `-race`.
- `grpcdifftest/run.sh -race`: real mode and model mode.
- The codec tests: shapes against descriptors and the Go structs; about 69k random values
  byte-exact; real encodings decoded into every type, fresh and pre-filled; 40k mutated inputs;
  every field number with edge and malformed values of all wire types; depth at and past 10000;
  the panics. A hand mutation campaign broke the generator 30 ways and 29 were caught. The miss
  is a redundant check, so behavior does not change.
- pbcodec against protowire.
- `harness/pbcodec`'s own tests.
- `go vet` in both modes.

**The two-node example** (`grpcdifftest/example`): a server node serving Arith (Add, Div) and a
client node (4 goroutines × 200 rounds, 2 s deadlines), run as separate processes on loopback.
Each build runs it twice: directly, and through a proxy that cuts every connection every 30 ms.
The client reconnects; failed calls are allowed, wrong replies are not.
- Results: real, 800 Add and 684 Div succeeded clean; 776 Add and 673 Div with cuts. Model, 800
  and 684 clean; 776 and 680 with cuts. 0 wrong in every run. The 116 Div failures in the clean
  runs are the expected division-by-zero errors.
- The rig (network namespaces, tc/iptables) was not used: it changes the host's network
  configuration, which this task excluded. The proxy gives the reset and partition classes of
  faults at the API level.

## QuePaxa through Goose (scratch check, `scratchpad/qpgoose`)

QuePaxa translates unmodified against the models: Goose rejects nothing, and the whole stack
typechecks in Lean. That covers replica/src, proto/client, proto, common, configuration, and the
redis stub, yaml.v2 and ioutil.

Offline build (the kit's go.mod patch):
- grpc v1.56.2 → v1.84.0, protobuf v1.31.0 → v1.36.12, plus the cached x/net, x/sys, x/text and
  genproto/rpc versions.
- go 1.17 → 1.26; `go` raises it itself.
- go-redis v8 replaced by `harness/rpcmodel/goredis`, which lacks `FlushAll` (kvStore.go:39).
- yaml.v2 v2.3.0 from `cache/gomod`.
- montanaflynn/stats stubbed or `client/` left out.
- Real-build `go vet` needs `-copylocks=false -composites=false`; upstream copies messages by
  value.

The models lack no API QuePaxa needs. The codec covers 17 message types: 14 consensus and 3
client.

## What the QuePaxa kit will still need

- **Harness or Perennial models and specs**, none of which the grpc model provides:
  - a sync.Map model or spec (ClientBatchStore, the biggest gap);
  - `strconv.Atoi` (on the constructor path);
  - package-level `math/rand` Seed and Intn;
  - `time.Time.UTC`, `Duration.Milliseconds` and `Duration.Microseconds`;
  - `sort.Ints` and `strconv.FormatInt` (leader mode 2 only);
  - `fmt.Println` and `fmt.Sprint`;
  - io/ioutil and yaml.v2 as names-only with no-op inits.
- **kit.toml:** `[protobuf]` listing the 17 messages (`pbgen.py --from-pb` drafts it), the
  `.pb.go` goose configs, and the trusted no-op init Lean files of decision 9.
- **The model-mode modfile in goose.sh and the kit's test commands.** kitgen does not yet write
  `go.model.mod`.
- **The adapter:** replace `replica/main.go` (flags, os.Exit), use leader mode 0/1 and benchmark
  mode 0, and avoid client status operations, which reach os.Create and log.Fatal.
- **Decision 7's consequence.** `recorder.go` panics when `Serve` returns an error, and under the
  net model `Serve` can return. Options: a marked workaround in the run; a net-model refinement
  (Accept errors on an open listener are temporary, a claim about Linux and Go to be tested); or
  the model retrying forever. The last would be unsound against real Go's non-temporary errors.
- **`server.go:116`'s `os.Exit` after a failed `grpc.Dial`.** Unreachable: the model's Dial with
  `WithInsecure` never fails (`Dial.spec`).
- **Proofs of the generated `_Consensus_*_Handler`s and `GRPCConnection`'s methods**
  (`handlerOk`), and `kitCodecOk` of the generated codec. Both are the run's.

## Results

**Proofs.** All the model's specs are proved over the net model, with no `sorry` and no
hypotheses left. `harness/lean/Harness/Proof/grpc` is 15 files, about 5,600 lines. `build.sh`
builds the whole harness, and `Axioms.lean` prints 211 theorems, none with `sorryAx`.

Proved:
- **Package initialization** of all 8 packages.
- **protobuf model:** `SetCodec`, `getCodec`, `Marshal`, `Unmarshal`, `MarshalValue`,
  `UnmarshalValue`.
- **status and codes:** `New`, `Error`, `Status.Code`/`Message`/`Err`/`String`, `FromError`,
  `FromContextError`, `Code`, `codes.Code.String`, and the fact that status errors have an
  `Error()`.
- **Server:**
  - `NewServer` and `RegisterService` (owner token, `descOk` with `handlerOk` per method).
  - `Server.call`: dispatch by `/service/method`, with the `dec` closure proved to meet `decOk`.
    It returns `(code, msg, reply)` with code 0 ⇒ `Φ reply`, and every code a `codes.Code`.
  - `handle`, `cancelCall`, `serveConn` (a fresh `WithCancel` context per call, canceled on
    return, on the client's cancellation and at connection end).
  - `Serve`: returns only with a non-nil error.
- **Client:**
  - `Dial`/`DialContext`/`NewClient`: a client connection iff some option sets credentials, else
    `errNoTransportSecurity`.
  - `ClientConn.Invoke`. Premises: `isContext ctx`, `W.MS a fm = some S`, the request's encoding
    premise with `S bs Φ`, and the reply's decoding premise. On `nil`, it returns `Φ rep` of the
    one handler run and the decoded reply. Otherwise it returns a status error and gives back
    the request's resources or premise and the decoding resource or a failed decoding. The
    deposit is lost, so the handler ran at most once.
  - `ClientConn.Close`.
  - Internals: the transport's `send`, `cancel`, `input` and `isShutdown`, and `getTransport`
    with connection registration.
- **Set-up:** `grpcWorld_alloc`, `grpcAddr_set`.

How the work was split:
- I wrote and proved the wire layer, the package inits, the protobuf model's specs and
  `NewServer`/`RegisterService`.
- Three subagents proved the rest: status, the server loop, and the client.
- I then removed the client's one remaining premise (`codesOk`): `answerRes` now records that an
  answer's code is a `codes.Code`, and the client learns it when it collects the answer.

**Axioms.** No new axioms. Every grpc theorem has 222: the net model's 216 (the
`TCPConn.Read.wp_proof` probe) plus 6 names-only types of Perennial's `fmt`. The `proto` specs
have 12. Before this work, the net/rpc model's `Client.Call.wp` also had 216.

**Go.**
- The two Go models: 1,250 lines. pbgen.py: 1,502 lines. pbcodec.go: 350 lines.
- `grpcdifftest/run.sh -race` passes in both modes: difftests, codec tests, the pbcodec tests
  against protowire, and the two-node example.
- `go vet` is clean in both modes, and existing kits' `kitgen --check` still pass.

**Open.**
- A Lean example proof of a two-method service over these specs (the Go example exists). The
  client and server specs are what such a proof would use.
- kitgen does not yet write `go.model.mod`, or the model-mode flags into goose.sh and the test
  commands.
- The `.pb.go` trusted no-op init files (decision 9) are per kit and not yet generated.
- Decision 7's Serve-error consequence for QuePaxa.
- `Errorf`/`Newf` are not specified (only `Error`/`New`), because `fmt.Sprintf`'s arguments need
  `ArgsWf`. QuePaxa's `Unimplemented*` methods call `Errorf`, but they are never reached, since
  `GRPCConnection` implements every method.
