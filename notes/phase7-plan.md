# Phase 7: etcd's gRPC, net and net/http axioms as theorems over the models (plan, Draft)

**Superseded where they differ by `notes/phase7-endstate.md`** (2026-11-24): the end state (one call
protocol for unary calls and streams, heap-free stream entries, `grpcServeTok` in one form, bridges
serving their target's table), the interim switch, the overnight decisions and the work plan. This note
keeps the history and the S2 and S5 drafts.

2026-11-21, claim #24. Phase 7 of `notes/dsverify-net-port-plan.md`, planned on its own as that section
says. Coordination: #10's `grpc3` (grpc's resolver, `resolver/manual`, `attributes`, `serviceconfig`,
etcd's `client/v3/internal/resolver`) and `http3` (`Proof/net/http/{Axioms,Boundary}.lean`,
`Proof/net/textproto/Header.lean`, rafthttp's `Codec`, `snapshotHandler.ServeHTTP`) land what they
have and then release the area to #24 (coordinator, #10, 2026-11-21). Nothing below edits those files
before that.

## What there is (inventory, `lean` at `ed897615f5`)

102 of `etc/tcb-baseline.txt`'s axioms mention grpc, net or http: 15 package-init axioms
(`initFuncsOk`/`opaqueInitsOk` of grpc's packages, net, net/http, net/url, `toGRPCErrorMap_init`), and 87
others. `etcd-all.txt` (`etcd_safe`) holds 99 of the 102. By kind:

- **Vocabulary**, axiomatized predicates with no definition: grpc's `grpcSrvNew`, `grpcAddrIsRaw`,
  `grpcSrvCfgRaw`, `grpcSrvLink`, `grpcConnsLink`, `grpcReplyTo`, `grpcConn`, `grpcResolverAt`,
  `grpcWrotePeer`, `grpcDialOptIs`, `grpcSrvOpt`, `grpcProtoCodec`, `grpcStatsHandlerOk`,
  `grpcHealthSrv` (`Proof/google_golang_org/grpc/Inv{Grpc,GrpcServer,GrpcRun,Dial}.lean`); net's
  `netAddrFree`, `netListenerAt`, `httpProtoFree` (`Proof/net/InvNet.lean`); and net/http's `opaque`s
  in `Proof/net/http/Boundary.lean` (`httpProtoAtRaw`, `respReader`, `bodyReader`, `respWriter`, ...: not
  axioms, so not in the TCB lists, but as uninterpreted).
- **Transport and connection**, over that vocabulary: `grpc.NewServer`, `Server.RegisterService`,
  `grpc.start`, the stage-B names `grpc.model.{acceptRun,acceptRunConns,respond,finishStream}` (with
  the trusted `Server.Serve` body), `NewClient`, `ClientConn.Invoke`, `ClientConn.NewStream`,
  `etcdResolver_grpc`; `net.Listen`; net/http's `reserve`, `register`, `Serve_ok`, the response
  writer, the body readers, the client (`RespClose*`, `ReadAll_resp_ok`, `ReadFull_resp_ok`,
  `CloseIdleConnections_ok`, `transport.NewTimeoutTransport`), the mux.
- **Leaves**, Go code the models keep verbatim: grpc's option constructors (`With*`, `MaxRecvMsgSize`,
  `ChainUnaryInterceptor`, ...), `CustomCodec`, `StatsHandler`, health, the prometheus interceptors,
  `ClientConn.Target`; net/http's `NewRequest`, `WithContext`, `URLString*`, `ReadAll`. Their *posts*
  are in the vocabulary's terms, so they become provable once the vocabulary is defined.

The protocol facts the vocabulary gives clients, which the model proofs must re-establish: a
connection reaches only the server listening at the dialed address; a handler runs at most once per
attempt (`grpcInvokerOk` consumes the call's spec once; `respond` consumes the exclusive
`grpcReplyTo`); a success returns the handler's reply; errors are in `clientErrTys`; a stream's two
directions are queues (`InvGrpcStream.lean`: in order, no loss or duplication, `io.EOF` only after the
peer's close and everything received); net/http's closed world (a request a server gets came from a
program's `RoundTrip`), at most once for `onceOnly` requests, statuses the handler's or Go's own, reads
a prefix of what the handler wrote.

## The two couplings that decide the order

1. **grpc's translation is independent of the network.** The model (`models/grpc`) has grpc-go
   v1.84.0's API and keeps its option, server-construction, interceptor and stream-wrapper code
   verbatim. Project `etcd` can take grpc's source from the model instead of the module cache (a
   `replace` in the translation's module file, as `models/grpc/gomodel.py` does for Go builds), under
   the same `Code/google_golang_org/grpc*.toml` (names-only but for what is proved). Then the leaves
   and server construction are provable over the model's bodies without any network semantics.
   Checked 2026-11-21: goose translates all 51 of the model's packages (71k Lean lines) with only two
   refusals: a labeled `continue` (`mem.ReadAll`, `health/client.go`) and `unsafe.StringData` in four
   generated `.pb.go` descriptors (protobuf plumbing, names-only as in etcd today). Whether the output
   compiles depends on the standard-library and protobuf names it calls; not built yet.
2. **`net` is coupled to the deployment statement.** The transport-level axioms (`Invoke`, `Serve`,
   `grpc.start`, `net.Listen`, all of net/http's server and client) can only become theorems over the
   net extension's `Conn`/`Listener`. The main tree's `net` is names-only today, over the axiomatized
   `netAddrFree`/`netListenerAt`, and every etcd closed theorem runs in **one process with no net
   extension** (`etcdFsExts := ⟨[idIssueExt, Fs.fsExt]⟩`,
   `examples/lib/etcdstart/FsExts.lean:46`; `etcd_safe` is eleven examples on separate clusters in one
   process). Making `net` the part's means adding the net extension to every etcd program's
   extensions, and getting the addresses' ownership from a deployment plan instead of the
   axiomatized premise `addrsUnclaimed` (`Proof/runtime/Start.lean`). That is a statement change for
   `etcd_safe` and every collection above it: the user's decision (below).

## Slices

Each lands on its own through the queue, with `etc/tcb-report.py --check --update` and the
collections' baselines saying what it removes.

- **S0, prerequisites.** (a) Project `etcd`'s grpc from the model: the `replace`, `etc/goose.py`'s
  handling of a module model (it has `std_models` for standard-library models; this is the module
  case), `etc/goose.py --check` with it, and `Code/google_golang_org/grpc*.lean` regenerated: no
  axiom removed, every proof still building (the model's `dialOptions`/`serverOptions` differ from
  v1.84's by a few fields: `models/diff.py grpc`). (b) The two goose refusals worked around in the
  model (`mem.ReadAll`'s labeled `continue` rewritten; the `.pb.go` descriptors names-only).
  Waits for `grpc3`'s release.
- **S1, server construction and options** (about 18 axioms). Define `grpcSrvOpt`, `grpcDialOptIs` and
  `grpcSrvNew` over the option closures' effect on `dialOptions`/`serverOptions` and the `Server`
  struct's fields; prove the option constructors, `NewServer`, `Server.RegisterService` over the
  model's bodies; then health (`RegisterHealthServer`, `grpcHealthSrv`) and `grpcProtoCodec` (as
  `models_lab.pbcodec`'s `PbCodec`, phase 5 item 1). `StatsHandler`/`otelgrpc.NewServerHandler`: the
  model removed stats handlers (a `NotModelled` panic), but etcd installs one
  (`v3rpc` `Link.lean`), so either the model keeps the stats-handler calls (decided in S1; the
  handler's methods are then the program's code) or the theorem would be vacuous there. No network.
  **S0 landed** (`715d5e6753`, 2026-11-21). **S1, server side (branch `phase7-s1`, 2026-11-21).**
  `grpcSrvOpt v k` is a definition (`Proof/google_golang_org/grpc/InvGrpcServer.lean`): `v` is a
  `*funcServerOption`, read-only, whose closure's persistent WP over a `p ↦ so` does `k`
  (`srvOptFnOk`): `.neutral` keeps the chains and the stats handlers; `.chainUnary`/`.chainStream`
  own the chain they append to; the new kind `.stats h` owns `statsHandlers`. A kind owns what its
  closure reads, so `StatsHandler`'s restated axiom stays true: stated as `.neutral` it would assert a
  WP of an `append` reading a slice the closure does not own, false for an arbitrary `so`. Proved
  over the model's bodies (`etc/goose.py`'s grpc translate list): `MaxRecvMsgSize`, `MaxSendMsgSize`,
  `MaxConcurrentStreams`, `KeepaliveEnforcementPolicy`, `ChainUnaryInterceptor`,
  `ChainStreamInterceptor` (one recipe: `wp_fupd`, `ipersist` of the captured cells,
  `wp_func_lits`, step into `newFuncServerOption`, then the closure; the chains through
  `wp_slice_append`). Still axioms, restated: `NewServer` (`[∗ list]` premise), `CustomCodec`,
  `StatsHandler` (`.stats h`). For `serverOptions` to be a translated struct, grpc's imports gained
  `time`, `io` (the `Compressor`/`Decompressor` interfaces of its `cp`/`dc` fields), `credentials`,
  `keepalive` and `stats`, and the model's `serverOptions` lost three fields whose types are other
  packages': `binaryLogger` and `inTapHandle` (their options panic when `NewServer` applies them,
  where the model's `NewServer` panicked on them before) and `bufferPool` (the server reads
  `mem.DefaultBufferPool()`, grpc-go's default; the option setting another pool panics), so that
  `tap`, `internal/binarylog` and `mem` stay untranslated, with no init axiom of theirs (a first
  attempt translating `mem` types-only added its two init axioms, which the land queue's tcb gate
  rightly refused; S2 translates `mem` with its pools). Trust base: −7 (the six, `grpcSrvOpt`).
  Users adjusted: v3rpc's `Server` spec (`[∗ list] v ∈ gvs, grpcSrvOpt v .neutral`) and proof, the
  `etcdstart`/`cluster3` callers. **Server stats handlers in the model (2026-11-22, branch `phase7-stats`).** The model's server
  calls a stats handler as grpc-go does, which kaashoek's `etcd_safe` server needs with tracing on:
  per connection `TagConn`/`ConnBegin`/`ConnEnd`, and per call `TagRPC`, `InHeader`, `Begin`,
  `InPayload`, `OutHeader`, `OutPayload`, `OutTrailer` and `End`, in grpc-go's order, with grpc-go's
  fields except `InHeader.WireLength`. That one is an HPACK size, given by a new choice point,
  `modelChooseLength`. `internal/grpcdifftest/stats_test.go` checks the sequences of a unary call, a
  failed call and the stream kinds against grpc-go's. One visible difference: a connection per stream
  means one `ConnBegin`/`ConnEnd` pair per call. The trusted claim is narrowed in `models/README.md` to
  programs whose behavior does not depend on how many connections carry their calls; otelgrpc's
  `TagConn`/`HandleConn` do nothing. Client stats handlers still panic `NotModelled`. **The dial side (2026-11-22,
  branch `phase7-dial`).** `grpcDialOptIs o d` is a definition (`InvDial.lean`): a read-only
  `*funcDialOption` whose closure's persistent WP over `p ↦ dopt` sets what `d` sets
  (`dialOptSets`) and keeps the other descriptor fields (`dialOptsKeep`); `.resolvers` and
  `.perRPCCreds` own the slice they append to. `dialOptsAt`'s fact is a `[∗list]`. Proved over the
  model's bodies: `WithTransportCredentials`, `WithPerRPCCredentials`, `WithUnaryInterceptor`,
  `WithStreamInterceptor`, `WithResolvers`. `WithKeepaliveParams` stays an axiom (it calls grpc's
  logger), restated. For `dialOptions`/`connectOptions` to be translated structs: grpc imports `net`
  and `resolver` too (their instances moved before grpc's in the cache's `Base.lean`), and the model's
  dial structs name no type of `internal/backoff`, `internal/binarylog`, `channelz` or `mem`
  (`withBinaryLogger`, `WithChannelzParentID`, `withBufferPool` panic `NotModelled`; the reconnect
  backoff is `DefaultExponential`, a timing). Trust base −6 (the five, `grpcDialOptIs`). client/v3's
  `Client__dial*` proofs adjusted. Landed `bbc60799b2`. S1 ends here: `NewServer` and
  `RegisterService` move to S2 (2026-11-22). Proving them means defining `grpcSrvNew` over the model's
  `Server` (its services map, the chained interceptor), the predicate the stage-B `Serve` axioms
  (`acceptRun`, ...) read, so its definition is S2's server invariant; the `Server` struct is also
  opaque until grpc imports `internal/grpcsync` and the model's `traceEventLog` is dropped.
- **S2, the unary pair** (`NewServer`, `RegisterService`, `grpc.model.*`, the trusted `Serve` body,
  `grpcReplyTo`, `Invoke`'s attempt, `grpc.start`). **A resource for the callees (2026-11-22, proving
  session 2's request on #24):** the contracts S2 restates, the client interceptor chain and the attempt
  (`grpcInvokerOk`, as `ClientConn.Invoke`/`NewStream` use it), per-RPC credentials'
  `GetRequestMetadata` and the server interceptor chain (`grpcSrvChain`/`srvChainWP`), take a resource
  parameter the caller passes in and gets back (as `isTransporter tr Rd`), so that etcd's
  `Client.Endpoints`, `perRPCCredential.GetRequestMetadata` and `api.IsCapabilityEnabled` can trade it
  for an `RWMutex` reader slot (`/shared/tmp/ps2/rdslot/design.md`, rafthttp's `8f442de83b`); draft
  signatures go to #24 before the proofs (written: "S2 draft signatures (2026-11-23)" below). over `model_transport.go`/`model_wire.go` and the net extension's `Conn`,
  from dsverify's unary proofs (Q2). Needs S4's deployment, or an interim single-machine statement
  over `goose_dist_adequacy` with one machine, which keeps `etcd_safe`'s single process but adds the
  net extension.
- **S3, streams** (`NewStream`, the stream ends, `InvGrpcStream.lean`'s two queues as a fact about the
  connection's two byte streams through the model's framing).
- **S4, the deployment statement.** Each member a machine (one node per member), the client drivers
  machines or co-located; addresses from the plan (`DistDeploy`-like); `netAddrFree`, `netListenerAt`,
  `httpProtoFree`, `addrsUnclaimed` gone; restart examples over the crash adequacy.
- **S5, net/http.** The server first (`Serve_ok`, the response writer, `Flush`, the body reader, the
  mux) over the model's real server (the largest proof); `reserve`/`register` as a per-address
  protocol registry; then the client, which needs the `Transport.RoundTrip` model (it panics today,
  `models/net/http/transport.go:614`) and chunked request bodies (the snapshot;
  `models/net/http/transfer.go:575`). Waits for `http3`'s release. Before S5, the main tree's
  names-only `Code/net/http.lean` and the part's `Net/Code/net/http.lean` declare the same namespace,
  so one replaces the other (with S4).

## S2 draft signatures (2026-11-23)

These are the names S2's proofs will be stated against, written before any proof, for #24
(kaashoek's putget-dist, proving session 2). Branch `phase7-s2-design`, off `lean`. The groundwork
`a12d44ed4f` on `phase7-s2` (grpc's `Server` as a translated struct) is not merged here. Nothing
below is built. The Lean text is the intended statement, and `...` marks a body sketched in prose.
Library names are neutral: `Net.*`, `GooseLang/Ext/Net` and grpc's
`Proof/google_golang_org/grpc/`. etcd's names live in etcd's files.

### 0. Where the answer on #24 had to change

Most of the answer's shape holds:
- `grpcSvcAt` does not depend on any heap, and `isGrpcRpc`/`isGrpcRpcMd` are redefined as it.
- The deposit travels in the connection's protocol.
- The start fixes the address, and the member publishes `E` once.
- A success implies that `E` was published.

Four details of it do not work as stated:

1. **There is no saved predicate of the service.** Perennial's saved predicates store
   `A → IProp GF` for a countable `A` (`Perennial/Ghost/SavedProp.lean`: `savedPredOwn` stores
   `Φ ∘ decode`). A method's spec takes the caller's `Φ` and `Ψe`
   (`GrpcSpecMd := GrpcMd → Req.M → (Rep.M → IProp) → (GoString → IProp) → IProp`). That puts
   `IProp` in a negative position, so the spec cannot be saved.

   It does not need to be. The net library keeps an address's protocols as *parameters of its
   invariant* (`addrInvP a γa P Q`, set once by `addr_set_proto`). `listen_au` needs
   `addrProto a P Q`, so the protocol is fixed before the member listens, which is before `E`
   exists anyway. So **the service is a Lean term `Svc`, fixed when the address's protocol is
   set**. The deployment's start sets it: the top-level proof, before the machines run.
   - `Svc` may mention ghost names that the start allocates (`γE`), but never `E`.
   - What the member sets at run time is the publication of `E` at `γE`, which is a fact on
     etcd's side. `Serve` publishes nothing about the service.
   - So "the per-address service right" is the net library's own `addrUnset a`, spent by the start
     (§1.2's `grpc_addr_set`). The member receives `grpcAddrAt a Svc` already set.
2. **`envAt γE E` cannot agree on `E : apply.AEnv GF` itself.** `AEnv` holds:
   - `IProp`-valued fields (`Nx`, `Pk`, `RD`, `FS`, `RO`, `RW`, `Cp`, `BkTie`, `Wt`);
   - one field with `IProp` in a negative position (`ciC : IProp GF → w64 → Prop`);
   - values on the member's heap (`kv : GoInterface`, `f : GoFunc`).

   No camera of `GF` can hold a value whose type mentions `IProp GF`. So the agreement is over a
   countable **view** `ν : EnvView` (ghost names, ids, modes), with `E = etcdEnvOf ν`. It is
   `dghostVar γE .discard (some ν)` (§1.3). The specs that clients see must factor through the
   view (open question O1). `etcdstart`'s `env₀` and `envAgree` suggest they do: `envAgree` reads
   only `γs`, `γrev`, `Nx` and `cmp`.
3. **The spec in the table must not depend on a heap, and neither may the message models it is
   typed over.** The table is one Lean term that both machines hold. A spec built with a `HeapGS`
   means a different proposition on each machine. One example is a points-to at a server `Loc`:
   `kvOpAuOn s E …` takes the server's `s`.
   - The rule: an entry's spec takes no `HeapGS` (O2).
   - Its types are the **wire part** `ProtoWire` of the message models (`ty`, `M`, `tree`), which
     involves no heap.
   - `tree` is only in `ProtoMsgT` today. `ProtoMsg` gains it, so that `isGrpcRpcMd`, which is
     typed over `ProtoMsg`, can name it (O3).
4. **`Invoke`'s post gains nothing at the grpc level.** `envAt γE E` reaches the client through
   the spec that etcd puts in the table (`etcdPubSpec`, §1.3), not through a conjunct of grpc's
   spec. The caller's obligation is for *every* view published at `γE`, and its `Φ` names the
   view.
   - So "a success means `E` was published" follows from the spec's shape, with no ordering
     between machines.
   - A dial before the listener exists is the semantics' refused `Dial`. That is an
     `Unavailable` error in the error arm. Its description is not in `handlerDescs`, so it carries
     no `Ψe`.

There is also one scope cut: **streams stay on the old pair in S2** (§2.6). The stream
registration (`isGrpcStreamAt`, a WP of the handler) still depends on the server's heap, so it is
used only within one machine until S3.

### 1. The vocabulary

#### 1.1 Deposit slots (net library, neutral: `GooseLang/Ext/Net/Slot.lean`)

This generalizes `remote`'s slot (`Net/Proof/.../examples/lib/remote/Defs.lean`: `slotOf`,
`slotInv`, `slot_register`, `slot_claim`, `slot_done`, `slot_take`) so that grpc and remote share
it. remote can move onto it later; that is not part of S2.

**On `lean` ahead of S2's core** (2026-11-23, branch `s2-vocab`, for etcd-dist's interim axioms over
`grpcSvcAt`/`grpcAddrAt`): this file and `Proof/google_golang_org/grpc/InvGrpcWire.lean` (§1.2) as
built on `phase7-s2-core`, with base64's `rawStdEnc` (pure); definitions and proved laws, no axiom.
One change from that branch: `grpcAddrAt` sets the address's protocols to the opaques
`grpcCliPI`/`grpcSrvPI` (trusted text with no law, `notes/audit.md`; intended reading
`grpcCliP`/`grpcSrvP`), since over the defined protocols raw Go code dialing or listening on a grpc
address could write or read the model's frames and make an axiom over `grpcAddrAt` unsound; the
defined protocols and their parse laws stay as a library until S2's proofs of `Invoke` and `Serve`
put them in place. **The interface switch is done** (2026-11-24, branch `s2-switch`, option (A), the
user's request: "with the unproved parts as axioms, so etcd-dist can proceed"): `ProtoWire :=
⟨ty, M, tree⟩` (`ProtoMsg` gains `tree`; `protoEncodes`, opaque, in place of `enc`); `isGrpcRpcMd`
redefined over `grpcSvcAt` and `grpcReach`; `Server.Serve` an axiom over `grpcServeTok gs lis a Svc` and
`grpcServes` (with the stream-name clause, C3); the model `Serve`'s leaves retired; the single-process
start over Go's table (`grpcGoSvc`, `etcdTys`, `netAddrLeft`). Review: `notes/axiom-review/s2-interface.md`;
ledger: `notes/specs-only/ledger.md`, 2026-11-24. S2's proofs then retire `Serve`'s axiom and the
opaque protocols, which needs the dec-shaped run contract and F2's world premise (the review).
How they amend §1.1 and §1.2 (the deposit with the data frame, per-connection refusal, `msgReady`,
`ProtoWire.enc`, `grpcFieldsMd`) is §0a on `phase7-s2-core`, which lands with the rest of S2's
core. `headerListOk` and `SrvFrame.oversized` are F1's (§0a), whose model fix is on that branch too:
until it lands, `lean`'s model does not yet check `headerListOk` before writing a block.

There is one slot per connection, keyed by what the dialer's bytes say. grpc's transparent retries
need two laws that remote does not use:
- the acceptor **refuses**: it gives the deposit back;
- the dialer **withdraws**: it takes the deposit back when the acceptor can never have read enough
  to claim it.

```lean
namespace Net

/-- What the acceptor of a slot answered: bytes the dialer decodes, an error description, or
that it refused the deposit (gave it back). -/
inductive SlotOut where
  | ok (bs : List w8)
  | err (d : GoString)
  | refused
deriving DecidableEq            -- with a `Pos.Countable` instance

/-- The slot map's ghost name (made once, by `depSlots_alloc`). -/
class NetSlotGS where
  slots : GName

/-- A slot's names: the outcome (a dfrac ghost variable `Option SlotOut`, the acceptor's half
while it runs) and the dialer's token. -/
structure SlotNames where
  o : GName
  t : GName

variable [NetProtoGS] [σ : NetSlotGS] {K : Type} [Pos.Countable K]

/-- The slot map's invariant: every registered connection, with its dialer's `connFresh cn false`
(so a connection has at most one slot). -/
def depSlotsCtx : IProp GF := inv slotsN (∃ M : GMap Nat (SlotNames × Pos),
  ghostMapAuth σ.slots 1 M ∗ [∗map] cn ↦ _v ∈ M, connFresh cn false)

/-- The connection `cn` has the slot `γ`, with the key `k` (persistent). -/
def depSlotOf (cn : Nat) (γ : SlotNames) (k : K) : IProp GF :=
  ghostMapElem σ.slots cn .discard (γ, Pos.Countable.encode k)

/-- **A dialer's prefixes after which an acceptor may claim** (closed under extension). -/
structure SlotReady (ready : List w8 → Prop) : Prop where
  mono : ∀ a b, ready a → a <+: b → ready b

/-- **The slot's invariant** (persistent): `ready` the dialer's written prefixes after which an
acceptor may claim, `D` the deposit, `Φ` what the dialer gets for an outcome. States: registered
(`D`); claimed (the acceptor's `connFresh cn true` in it, the acceptor holding the outcome's other
half, `slotRunTok`); answered `o` (`D` back if `o = .refused`, else `Φ o`, or the dialer's token
once taken); withdrawn (the dialer's `sendTok` on `cn` frozen at a `W` with `¬ ready W`, and its
token). -/
def depSlotInv (cn : Nat) (γ : SlotNames) (P : Proto GF) (ready : List w8 → Prop)
    (D : IProp GF) (Φ : SlotOut → IProp GF) : IProp GF :=
  inv (depSlotN cn) (
      (D ∗ dghostVar γ.o (.own 1) (none : Option SlotOut))
    ∨ (connFresh cn true ∗ (dghostVar γ.o (.own (1/2)) (none : Option SlotOut) ∨
        ∃ o, dghostVar γ.o .discard (some o) ∗ ((if o = .refused then D else Φ o) ∨ token γ.t)))
    ∨ (∃ W, ⌜¬ ready W⌝ ∗ sendTok cn false P W ∗ token γ.t ∗
        dghostVar γ.o (.own 1) (none : Option SlotOut)))

/-- The acceptor's share of a claimed slot (exclusive). -/
def slotRunTok (γ : SlotNames) : IProp GF := dghostVar γ.o (.own (1/2)) (none : Option SlotOut)

/-- The slot answered `o` (persistent). -/
def slotDone (γ : SlotNames) (o : SlotOut) : IProp GF := dghostVar γ.o .discard (some o)

-- The laws (each at a mask `E` that contains the slot's and the map's namespaces):
theorem depSlots_alloc (E : CoPset) : ⊢ |={E}=> ∃ σ : NetSlotGS, depSlotsCtx (σ := σ)
theorem depSlotOf_agree (cn : Nat) (γ γ' : SlotNames) (k k' : K) :
    depSlotOf cn γ k ∗ depSlotOf cn γ' k' ⊢ ⌜γ = γ' ∧ k = k'⌝
/-- Register (the dialer, once per connection, with the fresh token its `Dial` gave). -/
theorem depSlot_register (cn : Nat) (k : K) (P : Proto GF) (ready : List w8 → Prop)
    (D : IProp GF) (Φ : SlotOut → IProp GF) :
    depSlotsCtx -∗ connFresh cn false -∗ D ={E}=∗
      ∃ γ, depSlotOf cn γ k ∗ depSlotInv cn γ P ready D Φ ∗ token γ.t
/-- Claim (the acceptor, with its fresh token, once a `ready` prefix was written). -/
theorem depSlot_claim (hr : SlotReady ready) (W : List w8) (h : ready W) :
    depSlotInv cn γ P ready D Φ -∗ connFresh cn true -∗ sentLb cn false W -∗ £ 1 ={E}=∗
      D ∗ slotRunTok γ
/-- Answer (`o ≠ .refused`), or refuse (giving `D` back). -/
theorem depSlot_answer (o : SlotOut) (ho : o ≠ .refused) :
    depSlotInv cn γ P ready D Φ -∗ slotRunTok γ -∗ Φ o ={E}=∗ slotDone γ o
theorem depSlot_refuse :
    depSlotInv cn γ P ready D Φ -∗ slotRunTok γ -∗ D ={E}=∗ slotDone γ .refused
/-- Take the answer (the dialer, with its token): `D` back on a refusal, else `Φ o`. -/
theorem depSlot_take (o : SlotOut) :
    depSlotInv cn γ P ready D Φ -∗ slotDone γ o -∗ token γ.t -∗ £ 1 ={E}=∗
      if o = .refused then D else Φ o
/-- Withdraw (the dialer, giving up writing at a `W` at which no acceptor can claim). -/
theorem depSlot_withdraw (hr : SlotReady ready) (W : List w8) (h : ¬ ready W) :
    depSlotInv cn γ P ready D Φ -∗ token γ.t -∗ sendTok cn false P W -∗ £ 1 ={E}=∗ D
```

`depSlot_withdraw` is sound for these reasons:
- A claim needs `sentLb cn false W'` with `ready W'`.
- The frozen `sendTok`'s `wHalf` bounds every lower bound by `W` (`wHalf_wLb_prefix`), so
  `W' <+: W`.
- By `SlotReady.mono`, `ready W` would follow, contradicting `¬ ready W`.

#### 1.2 grpc's service table, protocols and registration (`Proof/google_golang_org/grpc/InvGrpcWire.lean`, `InvGrpc.lean`)

```lean
/-- **A message type's wire part** (no heap): its Go type, its model, and the tree its model
stores as (what grpc's codec marshals: the bytes are `pbEncodeTree (tree m)`). -/
structure ProtoWire [GooseExts] where
  ty : go.GoType
  M : Type
  tree : M → VTree

/-- `ProtoMsg` gains `tree` (moved from `ProtoMsgT`, which becomes `abbrev ProtoMsgT := ProtoMsg`;
O3), and this projection: -/
def ProtoMsg.wire (T : ProtoMsg GF) : ProtoWire := ⟨T.ty, T.M, T.tree⟩

/-- The bytes of a gRPC message holding `m` (grpc's codec over protobuf-go; the payload of a data
frame after its 5-byte header). -/
def grpcMsgBytes (W : ProtoWire) (m : W.M) : List w8 := pbEncodeTree (W.tree m)

/-- **A unary method of a service**: its messages' wire parts and its spec (no `HeapGS`). -/
structure GrpcEntry (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  spec : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF

/-- **A service table**: the unary methods by full name (`"/etcdserverpb.KV/Put"`). -/
abbrev GrpcSvc (GF : BundledGFunctors) [GooseExts] := GoString → Option (GrpcEntry GF)
```

**The model's bytes** (`models/grpc/model_wire.go`). The constants and frame builders are Lean
functions of the Go code's:
- `clientPrefaceBytes`: the 24 bytes of `clientPreface`;
- `settingsBytes`: `[frameSettings]`;
- `headFrame fs`: `appendHeaderBlock nil frameHead fs`;
- `dataFrame bs`: `frameData :: 0 :: be32 bs.length ++ bs` (uncompressed);
- `closeFrame`, `cancelFrame`, `headerFrame fs`, `trailerFrame fs`, `resetFrame code`.

Over `fs : List (GoString × GoString)` (the header fields, as `headerField`s):
- `pathOf fs`: the `:path` value;
- `mdOfFields fs : GrpcMd`: what `operateHeaders` makes the run's incoming metadata (the fields
  whose keys are not reserved, `grpcReservedKey`);
- `statusOf fs : Option (w32 × GoString)`: `grpc-status` and `grpc-message`, decoded as
  `model_http_util.go` does.

```lean
/-- What a unary attempt deposits for the entry `e`: its request precondition at the attempt's
metadata (the caller's own spec converted with `grpcSvcAt`'s wand, under the later the slot needs). -/
def grpcDeposit (e : GrpcEntry GF) (md : GrpcMd) (m : e.Wq.M) (Φ : e.Wp.M → IProp GF)
    (Ψe : GoString → IProp GF) : IProp GF := iprop(▷ |==> e.spec md m Φ Ψe)

/-- What the attempt gets back for an outcome: a reply whose bytes are some `m'`'s, with `Φ m'`;
or a handler's error description with its `Ψe`. -/
def grpcSlotCont (e : GrpcEntry GF) (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF) :
    SlotOut → IProp GF
  | .ok bs => iprop(∃ m', ⌜grpcMsgBytes e.Wp m' = bs⌝ ∗ Φ m')
  | .err d => iprop(⌜d ∈ handlerDescs⌝ ∗ Ψe d)
  | .refused => iprop(True)

/-- A dialer's prefix after which the server may claim: the preface and the whole head. -/
def headReady (fs : List (GoString × GoString)) (W : List w8) : Prop :=
  clientPrefaceBytes ++ headFrame fs <+: W

/-- The slot of a unary attempt on `cn` (persistent): the head `fs` names `e`'s method, the
request's bytes are `bs` (some `m`'s), and the slot holds the deposit at `fs`'s metadata. -/
def grpcAttemptSlot (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (bs : List w8) : IProp GF :=
  iprop(∃ (name : GoString) (e : GrpcEntry GF) (γ : SlotNames) (m : e.Wq.M)
      (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF),
    ⌜pathOf fs = some name ∧ Svc name = some e ∧ grpcMsgBytes e.Wq m = bs⌝ ∗
    depSlotOf cn γ (fs, bs) ∗
    depSlotInv cn γ (grpcCliP Svc) (headReady fs) (grpcDeposit e (mdOfFields fs) m Φ Ψe)
      (grpcSlotCont e Φ Ψe))
-- `grpcCliP` and `grpcAttemptSlot` name each other: either one mutual definition, or
-- `depSlotInv`'s `P` parameter is dropped (the withdrawn state then holds `sendTok cn false _ W`
-- at an existential protocol, which `depSlot_withdraw` needs no more of).

/-- **What a client writes** on a connection to an address serving `Svc`: the preface; then a head
`fs`. If `fs` names a unary method of `Svc` (`unaryOf Svc fs`), the attempt's slot, one data frame
of the slot's bytes, the end of the request, and possibly a cancel (`unaryTail bs rest`: `rest`
is a prefix of `dataFrame bs ++ closeFrame`, or that followed by a prefix of `cancelFrame`). A head
of any other path (a stream, or a name `Svc` lacks) allows anything after it (S3's case, §2.6). -/
def grpcCliP (Svc : GrpcSvc GF) : Proto GF := fun cn W =>
  iprop(⌜W <+: clientPrefaceBytes⌝ ∨
    ∃ fs rest, ⌜W = clientPrefaceBytes ++ headFrame fs ++ rest⌝ ∗
      ((⌜unaryOf Svc fs = false⌝) ∨
       (⌜unaryOf Svc fs = true⌝ ∗ ∃ bs, ⌜unaryTail bs rest⌝ ∗ grpcAttemptSlot Svc cn fs bs)))

/-- **What a server writes**: its preface; then header and trailer blocks, at most one data frame
and a reset. Each frame that answers for the attempt's slot carries that answer: a data frame of
bytes `bs'` carries the slot's `.ok bs'`; a trailer whose status description `d` is a handler's
(`d ∈ handlerDescs`) carries `.err d`; a `REFUSED_STREAM` reset carries `.refused`. Frames that
claim nothing (an OK header, a status grpc makes itself, a `CANCEL` reset) need nothing. The slot
is the one of the client's head (`depSlotOf cn γ (fs, bs)`, unique per connection). -/
def grpcSrvP (Svc : GrpcSvc GF) : Proto GF := fun cn W =>
  iprop(⌜W <+: settingsBytes⌝ ∨
    ∃ frames, ⌜W <+: settingsBytes ++ (frames.map srvFrameBytes).flatten⌝ ∗
      [∗list] f ∈ frames, srvFrameOk cn f)
-- srvFrameOk cn (.data bs')        := ∃ γ k, depSlotOf cn γ k ∗ slotDone γ (.ok bs')
-- srvFrameOk cn (.trailer fs)      := ∀ c d, ⌜statusOf fs = some (c, d) ∧ d ∈ handlerDescs⌝ -∗
--                                       ∃ γ k, depSlotOf cn γ k ∗ slotDone γ (.err d)
-- srvFrameOk cn (.reset refused)   := ∃ γ k, depSlotOf cn γ k ∗ slotDone γ .refused
-- srvFrameOk cn _                  := True

/-- **The address `a` serves `Svc`** (persistent): its protocols are grpc's for `Svc`, and the
slot map exists. -/
def grpcAddrAt (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(addrProto a (grpcCliP Svc) (grpcSrvP Svc) ∗ depSlotsCtx)

/-- **The start law**: an unset address is set to serve `Svc` (the net library's
`addr_set_proto`). -/
theorem grpc_addr_set (E : CoPset) (a : GoString) (Svc : GrpcSvc GF) :
    ⊢ regCtx -∗ depSlotsCtx -∗ addrUnset a ={E}=∗ grpcAddrAt a Svc

/-- **The method `name` at `a` meets `Spec`** (persistent, no heap; it replaces
`grpcAddrIs a γ ∗ isGrpcRpcAt γ name Spec`): the table `a` serves has an entry for `name` at the
wire parts `Wq`, `Wp`, and a caller of `Spec` meets that entry's spec after an update. So the
registration is monotone (`grpcSvcAt_mono_upd`), as `isGrpcRpcMd_mono_upd` is today. -/
def grpcSvcAt (a name : GoString) (Wq Wp : ProtoWire)
    (Spec : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ (Svc : GrpcSvc GF) Spec₀, grpcAddrAt a Svc ∗ ⌜Svc name = some ⟨Wq, Wp, Spec₀⟩⌝ ∗
    □ ∀ md m Φ Ψe, Spec md m Φ Ψe ==∗ Spec₀ md m Φ Ψe)

theorem grpcSvcAt_of_addr (a name : GoString) (Svc : GrpcSvc GF) (e : GrpcEntry GF)
    (h : Svc name = some e) : grpcAddrAt a Svc ⊢ grpcSvcAt a name e.Wq e.Wp e.spec

/-- **Redefined** (every user's statement unchanged): -/
def isGrpcRpcMd {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  grpcSvcAt addr name Req.wire Rep.wire Spec       -- `Req.wire.M` is `Req.M` by definition
-- `isGrpcRpc`, `isGrpcRpcs`, `isGrpcRpcsMd` and their laws (`_md`, `_mono`, `_mono_upd`,
-- `_singleton`, `_of_all`) keep their text; the `_mono` laws are reproved from `grpcSvcAt`'s wand.

/-- **The server serves `Svc` with Go's chain `ics` and unary registrations `regs`** (persistent;
`Serve`'s obligation): every registered unary method has an entry in `Svc` at its registered
messages' wire parts, and its handler meets that entry's spec as a run (`grpcRunOkMd`, unchanged,
on the server's own heap). Entries without a registration are allowed (their callers get
`Unimplemented`, an error that carries no `Ψe`). A method that no caller of the theorem uses can
have the entry `grpcNoCall := fun _ _ _ _ => False`, which every handler meets. -/
def grpcServes (Svc : GrpcSvc GF) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(□ ∀ (name : GoString) (mh : GoFunc) (srv : GoInterface), ⌜(name, mh, srv) ∈ regs⌝ -∗
    ∃ (Req Rep : ProtoMsgT GF) (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg),
      ⌜grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep⌝ ∗
      ⌜Svc name = some ⟨Req.wire, Rep.wire, Spec⟩⌝ ∗ grpcRunOkMd #mh srv ics Spec)
```

**How a unary call travels.** The model has one stream per connection (`model_transport.go`).

1. **The client dials and exchanges prefaces.** The attempt dials `a` (`dial_au` at the
   `addrProto` inside `grpcAddrAt a Svc`). It gets `connEnd cn false (grpcCliP Svc) (grpcSrvP Svc)
   [] []` and `connFresh cn false`. It writes the preface, which meets `P` on its own, and reads
   the server's `settingsBytes`.
2. **The client registers its slot and writes its request.**
   - `newClientTransportStream` computes the head `fs` with `createHeaderFields`: the credentials'
     metadata, then the context's. This is where `grpcAttemptMd conn om (mdOfFields fs)` gets
     *proved*.
   - It converts the caller's `▷ Spec (mdOfFields fs) m Φ Ψe` into the deposit with `grpcSvcAt`'s
     wand.
   - It registers the slot (`depSlot_register`) with the key `(fs, grpcMsgBytes e.Wq m)`, which
     `Req.send inp m` and the codec give.
   - It writes `headFrame fs`, then the data and close frames (`SendMsg`, `CloseSend`). Each
     write's protocol fact is `grpcAttemptSlot`.
3. **The server accepts and claims.**
   - The server (`handleRawConn` → `HandleStreams`) accepts with `accept_au`, getting
     `connEnd cn true …` and `connFresh cn true`. It writes its preface and reads the head.
   - The protocol fact of `recvTok` gives the slot. `operateHeaders` dispatches, and
     `depSlot_claim` (at the read prefix, `headReady fs`) gives the deposit and `slotRunTok γ`.
   - The data frame's bytes are the key's `bs` (`depSlotOf_agree`). So grpc's decoder stores
     `e.Wq.tree m` (the codec's law, O7), and the run gets `grpcDecOk dec Req m`.
4. **The run answers.** `grpcServes` gives the handler's run contract at the entry. The run (the
   chain, then the handler) returns `Φ m'` with the reply, or `Ψe d` for a handler's error.
   `sendResponse`/`WriteStatus` first answer the slot (`depSlot_answer` at
   `.ok (grpcMsgBytes e.Wp m')` or `.err d`), then write the frame whose protocol fact is that
   `slotDone`.
5. **The client takes the answer.**
   - The client reads the reply's data frame, which gives `slotDone γ (.ok bs')`. `depSlot_take`
     with its token gives `∃ m', grpcMsgBytes e.Wp m' = bs' ∗ Φ m'`.
   - Its decoder stores the tree of the bytes, which is `e.Wp.tree m'` (O7), so it has
     `Rep.recv out m'`.
   - With the OK trailer, `Invoke` returns `nil` and `Φ m'`. On a trailer with a handler's
     description it takes `Ψe d` instead.

**At most once.** This maps the old "one deposit, one run" argument (`InvGrpcRun.lean`'s header)
onto the connection:
- **One run per deposit.** A deposit is in one slot, which belongs to one connection: the slot map
  keeps `connFresh cn false`. The slot is claimed once, because the claim keeps `connFresh cn true`
  (`connFresh_excl`). This is what `grpcReplyTo`'s exclusivity said, now a theorem.
- **(a) grpc's transparent retry.** The model retries an attempt in only two cases:
  - Its head did not reach the server whole (`newClientTransportStream`'s `n < len(b)`). The client
    applies `depSlot_withdraw` at the written `W`, where `¬ headReady fs W`. The attempt's
    `sendTok` is frozen and the connection is closed.
  - The server refused it before dispatch (`REFUSED_STREAM`). The server applies `depSlot_refuse`,
    and the client applies `depSlot_take` at `.refused`.

  Either way, the deposit is back with the client before the retry's new connection registers it
  again.
- **(b) No retry policy, hedging or `healthCheckConfig`.** This stays a premise of the client's
  connection (`grpcResolverAt`'s service config), as now. The proof of the model's `stream.go`
  now uses it rather than citing it: `shouldRetry` has no case for a processed stream without a
  policy.
- **(c) D7 is retired.** D7 said that every connection to a served address is a `NewClient`
  connection, and that grpc makes no calls of its own. Now the net library's protocol binds every
  writer of a connection to `a`, whoever dialed it, and a head of a unary method can be written
  only with a slot.
- An attempt that returns early leaves its deposit in its slot, unclaimed or with the run, as now.

#### 1.3 etcd's side (`Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/EnvPub.lean`, a defs module)

```lean
/-- **The client-facing view of a member's apply environment** (countable: ghost names, the
member's ids, the modes; O1 fixes its fields). -/
structure EnvView where
  ...
deriving DecidableEq             -- with `Pos.Countable`

/-- The member's environment from its view (the member's construction, `srvEnv`/`env₀`'s). -/
def etcdEnvOf (ν : EnvView) : apply.AEnv GF := ...

/-- Not published yet (exclusive; one per member, from the start). -/
def envPubTok (γE : GName) : IProp GF := dghostVar γE (.own 1) (none : Option EnvView)
/-- **Published: the member's view is `ν`** (persistent, one-shot). -/
def envAt (γE : GName) (ν : EnvView) : IProp GF := dghostVar γE .discard (some ν)
/-- The phrase of #24, over the view. -/
def envAtE (γE : GName) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ ν, envAt γE ν ∗ ⌜E = etcdEnvOf ν⌝)

theorem envPub_alloc : ⊢ |==> ∃ γE, envPubTok (GF := GF) γE
theorem env_publish (γE : GName) (ν : EnvView) : envPubTok γE ==∗ envAt γE ν
theorem envAt_agree (γE : GName) (ν ν' : EnvView) : envAt γE ν ∗ envAt γE ν' ⊢ ⌜ν = ν'⌝

/-- **A spec over the published environment**: its caller's obligation for every view published
at `γE` (the server, which holds `envAt γE ν`, instantiates it at its own). -/
def etcdPubSpec {Req Rep : ProtoMsg GF} (γE : GName) (S : EnvView → GrpcSpecMd Req Rep) :
    GrpcSpecMd Req Rep :=
  fun md m Φ Ψe => iprop(∀ ν, envAt γE ν -∗ S ν md m Φ Ψe)

/-- **What a member publishes for its clients**, fixed by the start (`Pub` is a Lean function of
the view: the putget invariant, the read names, ...): an invariant the start allocates, open to
every client, holding `□ Pub ν` once `envAt γE ν` holds (the member puts it in when it
publishes). -/
def envPubInv (γE : GName) (Pub : EnvView → IProp GF) : IProp GF :=
  inv envPubN (dghostVar γE (.own (1/2)) (none : Option EnvView) ∨ ∃ ν, envAt γE ν ∗ □ Pub ν)

/-- **etcd's service**, as a table: KV, Lease, Cluster, Maintenance, Auth, health's `Check`, and
every other unary method `v3rpc.Server` registers, with `grpcNoCall` for those no client of the
theorem calls. -/
def etcdSvc (γE : GName) (cid mid : w64) : GrpcSvc GF := fun name =>
  if name = go!"/etcdserverpb.KV/Put" then
    some ⟨pbPutRequest.wire, pbPutResponse.wire,
      etcdPubSpec γE (fun ν => (etcdPutSpec (etcdEnvOf ν) (viewRd ν) cid mid).md)⟩
  else if ... else none

/-- **The client's registrations before it knows the view**, and after (clientv3's statements). -/
def kvRegsPub (addr : GoString) (γE : GName) (cid mid : w64) : IProp GF :=
  iprop(isGrpcRpcMd addr go!"/etcdserverpb.KV/Put"
      (etcdPubSpec γE (fun ν => (etcdPutSpec (etcdEnvOf ν) (viewRd ν) cid mid).md)) ∗ ...)
theorem kvRegsPub_at (addr : GoString) (γE : GName) (ν : EnvView) (cid mid : w64) :
    kvRegsPub addr γE cid mid ∗ envAt γE ν ⊢
      client.kvRegsAt ⟨addr, etcdEnvOf ν, viewRd ν, cid, mid⟩
```

`kvRegsPub_at` is `isGrpcRpcMd_mono` with `envAt_agree`:
- Once the client holds the view, it has clientv3's `kvRegsAt`, and every clientv3 spec applies
  unchanged. It gets the view from its first call's `Φ`, which a `Pub` caller writes as
  `∃ ν, envAt γE ν ∗ …`.
- A call made before that is made at the `etcdPubSpec` form. The client proves its obligation for
  an arbitrary `ν` with `envAt γE ν` by opening `envPubInv`: agreement makes the invariant's
  content `□ Pub ν`.

The deployment start (S4's `NetStart`/`ServerStart`, which is kaashoek's) does the setup:
1. It allocates `γE` (`envPub_alloc`) and splits `envPubTok` into the invariant's half and the
   member's.
2. It allocates `envPubInv` and the slot map.
3. It sets the member's client address with `grpc_addr_set a (etcdSvc γE cid mid)`.
4. It hands the member `grpcAddrAt a (etcdSvc …)` and its half of `envPubTok γE`. It hands every
   client `kvRegsPub a γE cid mid` and `envPubInv γE Pub`.

### 2. The specs

#### 2.1 `grpc.NewClient`

The text is unchanged (`Spec/google_golang_org/grpc/NewClient.lean`).
`grpcConn conn addrs ics dopts Ok` becomes a definition (a theorem's post, not an axiom). It is
over:
- the model's `*ClientConn`: its read-only fields (the target's resolved addresses `addrs`, the
  composed chain `ics`, `dopts`, the credentials `credsOfDial ds` with their contract at `Ok`);
- an invariant for its state guarded by `mu` (the idle flag, the set of streams, the resolver's
  state);
- the net library's `regCtx` and the slot map `depSlotsCtx`.

For `connCredsOk` and `credsYield`, see O4.

#### 2.2 `ClientConn.Invoke`

The text is unchanged (`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`). It is proved over the
model's `call.go`, `stream.go`, `model_transport.go` and `model_clientconn.go`, under the net
extension: the spec file gains the section variables `[HasExt netExt] [NetProtoGS] [NetSlotGS]`.

The **new form of `grpcInvokerOk conn addrs Ok inv` is its current text** (`InvGrpc.lean:1895`).
The registration conjunct no longer depends on a heap because of the redefinition:

```lean
def grpcInvokerOk (conn : Loc) (addrs : List GoString) (Ok : IProp GF → Prop) (inv : GoFunc) :
    IProp GF :=
  iprop(□ ∀ (method : GoString) (Req Rep : ProtoMsgT GF)
      (_ : grpcReqModelOf GF Req.ty = some Req) (_ : grpcRepModelOf GF Rep.ty = some Rep)
      (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M)
      (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (om : GrpcMd)
      (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc) (R : IProp GF),
    {{ ⌜Ok R⌝ ∗ R ∗ isGrpcRpcsMd addrs method Spec ∗ metadata.outMD ctx om ∗
        ▷ (∀ md, ⌜grpcAttemptMd conn om md⌝ -∗ Spec md m Φ Ψe) ∗
        ctxOk ctx cd ∗ Req.send inp m ∗ ⌜Req.wireLen m < grpcMsgMax⌝ ∗
        Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn #opts)
    {{ (err : GoInterface), RET #err; R ∗ Req.send inp m ∗ ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            go_etcd_io.etcd.cache.v3.errCellOk err ∗ Rep.own out ∗ notLearnerErr err ∗
            ∃ d : GoString, go_etcd_io.etcd.cache.v3.descIs err d ∗
            ⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) →
              d ∉ go_etcd_io.etcd.cache.v3.refusalDescs⌝ ∗
            (⌜d ∈ handlerDescs⌝ -∗ Ψe d))) }})
```

What changes is what makes it true:
- The docstring's claims about grpc-go become the proof's, over the model. They are: one write of
  the request, transparent retry only for unprocessed streams, the error types, and the
  credentials running on the caller's goroutine.
- The model's own trusted claim (`models/README.md`: the model behaves as grpc-go does, as the
  program observes it) replaces them.
- A refused dial (no listener yet) is the error arm: `Unavailable`, a description grpc makes.
- The client machine needs nothing of the server's heap: `isGrpcRpcsMd` is `grpcSvcAt` at every
  address.

#### 2.3 `grpc.NewServer`, `Server.RegisterService` (`grpcSrvNew` defined)

The texts are unchanged (`Spec/google_golang_org/grpc/{NewServer,Server__RegisterService}.lean`),
proved over the model's `NewServer`/`register`. The axiom `grpcSrvNew` becomes this definition:

```lean
/-- **The server `gs` being built** (exclusive): the model's `*Server` before `Serve`. Its options
compose the unary chain `ics` and the stream chain `sics` (`chainUnaryServerInterceptors` has
already run: `opts.unaryInt` meets `grpcSrvChainAll ics`, `opts.streamInt` meets
`grpcSrvStreamChainAll sics`). Its services map holds the services `svcs`, whose method and stream
descriptors give exactly `regs` and `sregs` (by `descRegs`/`descSRegs` per service, in order). It
has no listener and no connection, `serve = false`, and its events, wait groups and `cv` are
fresh. -/
def grpcSrvNew (gs : Loc) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(∃ (so : serverOptions.t) (smap : Loc) (infos : GMap GoString Loc) (mu cv : Loc) ...,
    gs ↦ Server.mk so ... ∗ srvOptsOk so ics sics ∗ ownMap smap (.own 1) infos ∗
    ⌜infos.dom = svcs.toFinset⌝ ∗ ([∗map] sn ↦ si ∈ infos, srvInfoIs si sn regs sregs) ∗
    ⌜(regs.map Prod.fst).Nodup ∧ ...⌝ ∗ isMutex mu ... ∗ ... )
```

The helpers:
- `srvOptsOk` comes from S1's `srvOptFnOk` kinds.
- `srvInfoIs si sn regs sregs` describes the `serviceInfo`'s `serviceImpl` and `streams` map: the
  entries of `regs`/`sregs` whose names have the prefix `/sn/`, with unary methods wrapped by
  `wrapUnaryHandler` as the model does.

`RegisterService`'s `⌜sn ∉ svcs⌝` premise and `Serve`'s joint `Nodup` stay.

#### 2.4 `Server.Serve` and `grpc.start`

```lean
/-- **The right to serve `gs` on the listener `lis` at `a`** (redefined; it was the link, the
configuration and the size premise): the server built, the node's open listener at `a` (the net
library's), the address serving `Svc`, the server serving `Svc`, the stream half's facts (§2.6),
the names jointly distinct, and the replies' size premise. -/
def grpcServeTok (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(∃ (ics sics : List GoFunc) (svcs : List GoString)
      (regs sregs : List (GoString × GoFunc × GoInterface)) (l : w64),
    grpcSrvNew gs ics sics svcs regs sregs ∗
    isListener lis l ∗ netLis hL l a true ∗ netLisAt hL l a ∗
    grpcAddrAt a Svc ∗ grpcServes Svc ics regs ∗ grpcStreamHalf a sics sregs ∗
    ⌜((regs ++ sregs).map Prod.fst).Nodup ∧ grpcRepliesFit⌝)

abbrev grpc.Server.Serve.spec : Prop :=
  ∀ (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF),
  {{ grpcServeTok (GF := GF) gs lis a Svc }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"Serve"))
      (Val #lis))
  {{ (err : GoInterface), RET #err; True }}
```

`Serve` is now the model's code with its body, no longer the trusted `Server.Serve.impl`. The path
is `server.go`'s `Serve` → `handleRawConn` → `serveStreams` → `HandleStreams` → `handleStream` →
`processRPC`. The proof's invariants:
- Per accepted connection: §1.2's steps 3-4.
- Per server: `gs`'s maps guarded by `mu` (listeners, connections), the wait groups (thread tokens,
  `notes/bounds-plan.md`), and `quit`/`done`.

`grpc.start` is no longer the unary half's axiom: the unary half reads none of what it made
(`grpcAddrIs`, `grpcSrvCfg`, the link). It survives only narrowed to the stream half (§2.6).
`grpc.start'` and `grpc.serve` (theorems today) are replaced by two things: introducing
`grpcServeTok`, which is a definition with nothing to prove, and `grpcSvcAt_of_addr`.

#### 2.5 The stage-B leaves

| Leaf | In S2 |
|---|---|
| `grpc.model.acceptRun` | **Retired.** Its unary arm becomes `Serve`'s proof over the model. Its stream arm becomes §2.6's axiom. |
| `grpc.model.acceptRunConns` | **Retired.** The model's open connections keep serving in their own goroutines, so there is no `lisFailed` composite. |
| `grpc.model.respond` | **Retired.** It becomes `processRPC`'s `sendResponse`/`WriteStatus` over the model's transport, which answer the slot. |
| `grpc.model.finishStream` | **Retired** with the trusted `Serve`: the model's `processRPC` ends a stream. §2.6's axiom covers what the stream handler's return needs. |
| `Server.Serve.impl` (the trusted model), `model.runCall`, `model.serveRest`, the old form of `grpcServeTok` | **Retired.** |

#### 2.6 The stream half, until S3

A head of a stream method carries no slot (the `unaryOf … = false` arm of `grpcCliP`). The
server's proof of `processRPC` at a stream descriptor uses one narrowed axiom: the old pair's stream
arm, moved to the point of dispatch.

```lean
/-- **A dispatched stream** (an axiom until S3): on the server `γ` with Go's configuration `c`
(`grpcSrvCfg`, made by the narrowed `grpc.start`), a stream that the model's `HandleStreams`
dispatched for a path in `c.sregs` gives `processRPC` what `grpcAccepted`'s stream arm gives today:
the deposited stream registration (`isGrpcStreamAt γ name Up Spec`), the shared `□ Spec md γs Dn`,
the raw server end with both tokens at `[]`, grpc's composed stream interceptor, and `info`. -/
axiom grpc.streamDispatch ... :
  grpcSrvCfg γ c ∗ srvStreamHead st cn fs ∗ ⌜pathOf fs = some name ∧ name ∈ c.sregs.map Prod.fst⌝ ⊢
    |={⊤}=> grpcAcceptedStream γ c name st ...

def grpcStreamHalf (a : GoString) (sics : List GoFunc)
    (sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(∃ γ ics regs, grpcAddrIs a γ ∗ grpcSrvCfg γ ⟨ics, sics, regs, sregs⟩)
```

Its soundness argument is the stream bullet of "The pair". It is sound only where the client's
`NewStream` runs on the server's heap. `NewStream` is still an axiom, consuming
`grpcAddrIs a γ ∗ isGrpcStreamAt γ …`, and a stream registration is a WP of the server's handler,
so no other machine can hold one. Streams across machines (watch, lease keep-alive) wait for S3.

### 3. What changes for existing users; the axioms

**clientv3** (`Proof/go_etcd_io/etcd/client/v3/*`, 21 files mention `isGrpcRpc*`). No statement
changes:
- `isGrpcRpcMd` is redefined; `kvRegsAt` and the client specs keep their text.
- Proofs that use `isGrpcRpcMd_mono`/`_mono_upd`/`isGrpcRpcs_*` keep them; the laws are reproved.
- Two proofs outside grpc's files unfold `isGrpcRpcMd` down to `grpcAddrIs`/`isGrpcRpcAt`:
  - `InvLeaseGrant.lean:200`'s `isGrpcRpc_mono_with` (monotone with a persistent context). It is
    reproved from `grpcSvcAt`'s wand, with the persistent fact framed into it. Its statement stays.
  - `cluster3/Defs.lean:258-270` (the bridges' `grpcAddrIs` forwarding). This goes with O5.
- If O4 makes `grpcAttemptMd` an `IProp`, its users (the auth clients' `connCredsOk` proofs) change
  one premise.

What is new in etcd's files is §1.3.

**v3rpc's server** (`v3rpc.Server`). Its post (`grpcSrvNew` with etcd's `regs`) is unchanged, and so
are its handlers' proofs (`grpcMethodOkMd`, the adapter `grpcRunOkMd_of_pools`). The new
obligation, which goes in `etcdstart`, is `grpcServes (etcdSvc γE cid mid) ics regs`:
- from each handler's `grpcRunOkMd` at `etcdPutSpec (etcdEnvOf ν) …`, with `envAt γE ν`, by
  `grpcRunOkMd_mono` through `etcdPubSpec`;
- with `grpcNoCall` entries for the rest.

**`etcdstart`** (`Serve`, `Served`, `etcdKVAt_regs`, the callers in cluster3). Today the spec of
`etcdstart.Serve` *produces* `kvRegsAt` on the member, through `grpc.start'`/`grpc.serve`. Now:
- It takes `grpcAddrAt a (etcdSvc γE …)`, the member's half of `envPubTok γE`, and
  `envPubInv γE Pub`.
- It publishes (`env_publish`, putting `□ Pub ν` into the invariant) and returns `envAt γE ν`.

The single-process examples (the eleven of `etcd_safe`) need the net extension in their programs
and the start of §1.3 (`addrs_start`, `netProto_alloc`, `depSlots_alloc`). This is the plan's
coupling 2, under the user's decision of 2026-11-22 (one machine per member). An interim statement
on one machine, over `goose_dist_adequacy`, keeps their shape.

**Retired by S2** (from `etc/tcb-baseline.txt` and the trusted texts):
- `grpcSrvNew` (an axiom, now a definition);
- `grpcReplyTo`, `grpcSrvLink`, `grpcConnsLink`;
- `grpc.model.acceptRun`, `grpc.model.acceptRunConns`, `grpc.model.respond`,
  `grpc.model.finishStream`;
- `grpc.NewServer`, `grpc.Server.RegisterService`, `grpc.NewClient`, `grpc.ClientConn.Invoke`;
- `grpcConn` and `grpcConn_persistent` (now definitions);
- `grpcWrotePeer` (now a definition: the model's transport writes the peer);
- `credsYield` (opaque, now defined; O4);
- the trusted `Server.Serve.impl`;
- the world premise D7. It is no axiom, but a claim the proof cited that is no longer needed.

Of the vocabulary, `isGrpcRpcAt` and `grpcServerAt` lose their unary role: `isGrpcRpcAt` is
deleted, and `grpcServerAt` goes with `grpc.serve`.

**Kept by S2:**
- `grpcAddrIsRaw`, `grpcSrvCfgRaw`, `grpcAddrIs_agree`, `grpcSrvCfg_agree`, and `grpc.start`,
  narrowed to the stream half only and taking the net extension's listener in place of
  `netListenerAt`;
- the new `grpc.streamDispatch`;
- `ClientConn.NewStream` and the stream ends (S3);
- the codec (`grpcProtoCodec`, the laws of the decoder and the marshaller: O7), until phase 5's
  `PbCodec`;
- `grpcRepliesFit` (a named workload premise), and `noRefusalAt`/`noOtherRefusalAt` (opaque
  premises);
- `grpcResolverAt` and `etcdResolver_grpc` (grpc3), `WithKeepaliveParams`, `grpcStatsHandlerOk`,
  `grpcHealthSrv`, `promSrvMetrics`;
- the per-type registration axioms (`pb*T_reg`).

**Possibly added:** init axioms of `mem`, if its pools are translated with initializers that do not
translate. S1 avoided that, and S2 should too.

### 4. Open questions

- **O1. The view.** Two things to find out:
  - Which fields of `AEnv` the client-facing specs read: `etcdPutSpec`, `etcdRangeSpecE`,
    `putReplied`, `rangeReplyOk`, ... use `E.γs`, and what else?
  - Whether the member's `E` is a function of countable names (`etcdEnvOf ν`), with its predicate
    fields (`Nx`) fixed definitions over them.

  If a client-facing spec reads a predicate field that cannot be defined from names, that field
  needs a saved predicate beside the view (`savedPredOwn` over a countable domain, such as `Nx` over
  `mvcc.Log`).
- **O2. Specs in the table must not depend on a heap.** `#check @client.etcdPutSpec`, and the same
  for the others in `etcdSvc`, must show no `HeapGS` argument. The auth-on specs
  (`etcdPutSpecOn s E …`, over the server location `s` through `v3rpc.kvOpAuOn`) are suspect. A
  spec that needs the server's heap has to be split: the heap part stays in the server's run
  contract (`grpcMethodOkMd`'s bundle), and the client sees only ghost state.
- **O3. `tree` into `ProtoMsg`.** The change is mechanical: each `pbX` model defines its tree, and
  `ProtoMsgT` becomes an abbreviation. It touches every message model. The alternative is for
  `isGrpcRpcMd` to quantify over the trees (`∃ tq tp, grpcSvcAt … ⟨Req.ty, Req.M, tq⟩ …`). That
  needs a registry of trees per Go type, independent of the heap, so that the client's `Req.tree`
  can be shown to be `tq`: more trust, not less.
- **O4. `credsYield`.** The attempt contract's `grpcAttemptMd conn om md` rests on the opaque
  `credsYield conn cm`, which the proof over the model cannot produce. Two options:
  - **Proposal:** an `IProp` `credsYieldI conn cm`, persistent: `cm` is in a ghost set of the
    connection's credential outputs, which `grpcConn` names and whose invariant ties it to
    `connCredsOk`'s `□ Q cm`. `grpcAttemptMd` becomes an `IProp` premise in `grpcInvokerOk`, so one
    premise changes for its users.
  - Keep `credsYield` Prop-valued, defined by the connection's list of credentials. This works only
    if every user needs only `connCredsOk`'s `[]` case (to check).
- **O5. Bridges.** `bridge.New` (the partition examples, linkv3p) forwards bytes between two
  connections. The client's slot is on the client→bridge connection, but the server claims on the
  bridge→server one. A bridge proof would claim on one side and re-register on the other, at the
  ghost level, once the forwarded bytes hold a whole head; the bridge's address serves the target's
  `Svc`. Until then the bridged examples keep their current axioms (they run in one process).
- **O6. Wildcard listeners** (branch `net-wildcard-listen`, `02fae64e64`, not yet on `lean`). A
  wildcard listener accepts on every address of its port (`lisAccepts`). `grpcServeTok` then needs
  `grpcAddrAt a' Svc` for each accepted address `a'`, with one `Svc` for all of them. `grpcSvcAt` is
  keyed by the dialed string, as `grpcAddrIs` is today.
- **O7. The codec.** The deposit's bytes are `pbEncodeTree (tree m)`. S2 needs two facts about
  grpc's codec:
  - marshalling a sender's `*T` holding `m` produces those bytes;
  - unmarshalling them is `storeInto ty l t`, where `pbEncodeTree t = bytes` determines `t` (decode
    after encode is the identity on trees).

  Phase 5's `models_lab.pbcodec` proves this for its own codec, but grpc's default codec is
  protobuf-go's. So S2 either installs that codec as the model's default (as phase 5 item 1 plans
  for `grpcProtoCodec`) or keeps the codec's two laws as axioms.
- **O8. The mask of `grpcDeposit`'s update.** The deposit is `▷ |==> spec`, from `grpcSvcAt`'s `==∗`
  wand. If converting a spec needs an invariant, the wand must be `={⊤}=∗` and the mask of the
  claim law adjusted. Opening `envPubInv` does not count: the *client* does it before depositing.
- **O9. One machine in the interim.** Until S4, S2's theorems can serve the single-process examples
  only by adding the net extension to them (coupling 2). Whether kaashoek's `NetStart`/`ServerStart`
  lands first decides whether S2 states anything for `etcd_safe`, or only for putget-dist.

## S5 draft signatures (2026-11-24)

Proving session 2 (claim #18), on #24: both halves of S5 over the net/http model (`models/net/http`,
translated into `Net/`, project `models-net`), after `models-rpc-http` (`af1e3f4675`). Written before
any proof; nothing below is built. Branch `prove-ps2-s5srv/2026-11-24`. The Lean text is the intended
statement; `...` marks a body sketched in prose.

### 0. Decisions this draft takes as given

- **No new trusted text.** The client half un-deletes upstream code: `Transport.roundTrip` (deleted to a
  `notModelled` panic, `models/net/http/transport.go:614`) and the chunked reader (`modelChunked`,
  `textproto_model.go:169`, back to `internal.NewChunkedReader`). Both shrink the model's diff. Goose
  takes `net/http/internal` (`chunked.go`, `sniff.go`) from the toolchain, translated with its bodies.
- **Sticky read errors** are the net extension's (D1 v3.5, landed with `models-rpc-http`). No
  `connReader*` file and nothing of `GooseLang/Ext/Net` is edited.
- **`notModelled`.** No spec relies on reaching one (`internal/gomodel.Stuck()`, perennial#694, once
  pinned). The protocol below makes the model's `notModelled` head-parser branches unreachable: every
  head a program's client writes is one the model parses (`hdrBlockOk`).
- **Threads.** `Server.Serve` forks one goroutine per connection (`conn.serve`), and `connReader`
  forks the background read per request. Perennial's fork rule (`wp_fork_tok`) gives each forked
  thread a `threadTok`, returned at its exit. So the handler borrows **its connection goroutine's own
  token**: no `handlerPool`, unlike `SpecPlan`'s `Serve.spec` (§5, C1). The background read runs on its own.
- **One generation.** Net's protocols are fixed per run; `SpecPlan`'s `protoFam` (one protocol per
  crash generation) waits for S4's crash story. Here `protoAt` is the run's.

### 1. The HTTP vocabulary: `SpecPlan`'s, defined

The client-facing vocabulary is `SpecPlan/Spec/net/http/Api.lean`'s, with its opaques defined over the
model and the net extension. So the main tree's `Proof/net/http/{Boundary,Axioms}.lean` can move onto
it at S4 (§4).

```lean
-- SpecPlan's, unchanged: HReq (meth, host, path, hdr), Proto (hreq, bodyPre, body, resp), onceOnly,
-- hdrView, srvKeys, pathUnder, readerAt's Pre/Φ over IProp.
structure Proto (GF) where
  hreq    : HReq → GName → IProp GF
  bodyPre : HReq → GName → List w8 → IProp GF
  body    : HReq → GName → List w8 → IProp GF
  resp    : HReq → GName → w64 → List (GoString × GoString) → List w8 → IProp GF

/-- What `reserve` asks of a protocol: the server's own answers (`srvStatuses`, with Go's fixed
bodies and the two `srvKeys` headers) are in `resp`, and `resp` is prefix-closed in `w`. -/
def Proto.ok (P : Proto GF) : Prop := ...
```

**The requests a program's client writes** (`hreqOk R`, pure): `GET` or `POST`; `R.path` a
`reqPath` (`RequestDefs.lean`: `/` and the bytes `url` leaves alone, which rafthttp's paths are); `R.host`
an ASCII `host:port` that is not IPv6 (so the Transport dials exactly `R.host`: `canonicalAddr`); the
headers `hdrBlockOk` after canonicalization, with none of the keys the Transport writes itself (`Host`,
`Content-Length`, `Transfer-Encoding`, `Connection`, `User-Agent`, `Accept-Encoding`) and **no
`Expect`** (§5, C3). rafthttp's requests are all of this kind.

**Framing** (pure, `Net/Proof/net/http/Wire.lean`):

```lean
inductive Frame | none | len (n : Nat) | chunked
/-- A chunked body's wire: each chunk (non-empty) `hex(len) ++ "\r\n" ++ c ++ "\r\n"`, then, if
`fin`, `"0\r\n\r\n"`. -/
def chunkedWire (cs : List (List w8)) (fin : Bool) : List w8
/-- A request's head as `Request.write` writes it: the line, `Host`, `User-Agent`, the framing's
header, `R.hdr`'s lines sorted by key, `Accept-Encoding: gzip`, the empty line. -/
def reqHeadWire (R : HReq) (f : Frame) : List w8
/-- A response's head as `chunkWriter.writeHeader` writes it: the status line, then a header block
`hc` with `srvView hs hc` (the handler's committed `hs`, plus some values at `srvKeys`: `Date`,
`Content-Type` (sniffed), `Content-Length` or `Transfer-Encoding: chunked`, `Connection`). -/
def respHeadOk (st : w64) (hs hc : List (GoString × GoString)) (f : Frame) : Prop
```

**A connection's ghost state** (`HttpConnNames`, `httpConnInv`, shaped like net/rpc's `connInv`,
`Net/Proof/net/rpc/Proto.lean`):
- the requests in the order written, a mono-list of `(R, τ, f)`;
- the server's count `k` of request heads taken, half with the serving thread. Taking request `k`
  moves its ticket out, so a ticket goes to at most one handler run;
- each `onceOnly` request's `reqTicket τ`, deposited by the client's write loop with the request's
  **first byte on the wire**. A request of which nothing was written keeps its ticket, which is what
  makes Go's `nothingWrittenError` retry of a `POST` sound (`shouldRetryRequest`).

**The byte protocols** of an HTTP address (`Net.Proto := Nat → List w8 → IProp`):

```lean
/-- What a dialer of `a` writes: a prefix of its requests' wires, in order; each request
`hreqOk`, with `□ P.hreq R τ`, and its body bytes (after the head) a stream with `□ P.bodyPre R τ B`
of each prefix `B` sent, and `□ P.body R τ B` once complete (the length reached, or the chunked
terminator). -/
def httpReqP (P : Proto GF) (a : GoString) : Net.Proto GF := fun cn bs => ...
/-- What an acceptor at `a` writes: a prefix of responses, the `i`-th one answering the `i`-th
request (`R, τ`, from the mono-list's lower bound): a head `respHeadOk st hs hc f` and a body framed
by `f` (length, chunked, or none), whose bytes `w` meet `□ ∃ w', w <+: w' ∗ P.resp R τ st hs w'`;
or a server answer (`srvStatuses`) that ends the connection. -/
def httpRespP (P : Proto GF) (a : GoString) : Net.Proto GF := fun cn bs => ...

/-- `SpecPlan`'s `protoAt`: the address `a` serves HTTP with `P` (persistent). -/
def protoAt (a : GoString) (P : Proto GF) : IProp GF :=
  iprop(addrProto a (httpReqP P a) (httpRespP P a) ∗ inv httpRegN httpRegInv ∗ ⌜P.ok⌝)
```

The `SpecPlan` laws then become theorems: `reserve` from `addr_set_proto` (`addrFree a := addrUnset a`;
a wildcard listener through `lis_set_proto`), `addrFree_protoAt_excl`, `reqTicket_alloc`/`_excl`. The
main tree's axioms `reserve` and `register` go with S4's swap.

### 2. The server half (`models/net/http/server.go`, `transfer.go`'s `body`)

**Server-side predicates** (definitions sketched):
- `srvReq r R rd`: `SpecPlan`'s `srvReq_fields` (`Method`, `URL.Path`, `Header` as `hdrRO` of the
  request's headers without `Host`, `Body` `rd` never `nil`, `RemoteAddr`).
- `readerAt rd Pre Φ r` for a request body: `rd` is `NoBody` (`r = []`, `Φ []`), or a `*body` over
  `io.LimitReader(bufr, n)` (length-framed) or over the chunked reader (§4), on the serving thread's
  `bufio.ownReader` of the connection's `recvTok` (`crStream`, `ConnReaderStream.lean`, in its body
  phase). The bytes read so far are the request's body prefix, so `□ P.bodyPre R τ r`. `EOF` comes only
  from the length reached or the chunked terminator, so `□ P.body R τ r`. Exclusive, and given to the handler.
- `respW w R τ P c hs bs`: `w` is the `*response` `rp`. If `c = none`, its `handlerHeader` map is
  `hdrMap` of `hs`, the commit's input. `rp.w` (a 2048-byte `bufio.Writer`) over `rp.cw` (the
  `chunkWriter`) over the connection's 4096-byte `bufw` over `checkConnErrorWriter` over the
  connection's `sendTok cn true (httpRespP P a) W`. The bytes on the wire, plus the two buffers,
  are the response head (once `cw.wroteHeader`) and the framed prefix of `bs`. Or the connection has
  failed (`conn.werr` set, the socket closed: every later write fails, and the client sees a cut
  response, which its reader reports as an error, never `EOF`).

**Specs** (statements as in `SpecPlan`, proved over the model):

| `SpecPlan` statement | the model's code it is proved over |
|---|---|
| `Serve.spec` (below) | `Serve`/`Server.Serve` (accept loop, `newConn`, `go c.serve`), `conn.serve`'s loop, `readRequest` (general heads, bodies), `serverHandler.ServeHTTP`, `finishRequest`, `shouldReuseConnection`, the answers `400`/`431`/`501`/`505`, the deferred `recover` |
| `respW_header.spec` | `response.Header` |
| `respW_writeHeader.spec` | `response.WriteHeader` (`checkWriteHeaderCode`) |
| `respW_write.spec` | `response.Write`/`write`, `bufio.Writer.Write`, `chunkWriter.Write`, `chunkWriter.writeHeader` (Content-Length when the handler ends within the buffer, otherwise chunked; `Date` from `appendTime`, `Content-Type` from `DetectContentType`; the remaining request body drained, at most `maxPostHandlerReadBytes`) |
| `respW_flush.spec`, `respW_flusher.spec` | `response.Flush`/`FlushError`, `chunkWriter.flush` |
| `readerAt_read.spec`, `readerAt_close.spec` (request bodies) | `body.Read`/`readLocked`, `body.Close` (the drain, early close), `registerOnHitEOF` with `startBackgroundRead` |
| `mux_handlerOk.spec`, `NewServeMux`, `Handle`, `muxOwn_freeze` | `ServeMux` (Go 1.22 patterns, literal path patterns only) |

```lean
/-- `http.Serve(l, h)` / `(&Server{Handler: h}).Serve(l)`: `l` the listener at `a`, `a` serving `P`,
`h` a handler of `P` (for every path, `pfx = "/"`). It returns only an error (the listener closed
or failed); each connection is served on its own goroutine. -/
abbrev Serve.spec : Prop :=
  ∀ (l h : GoInterface) (a : GoString) (P : Proto GF),
  {{ httpSrvEnv ∗ listenerAt l a ∗ protoAt a P ∗ handlerOk h P "/" }}
    (App (App (Val (@! net.http.Serve)) (Val #l)) (Val #h))
  {{ (err : GoInterface), RET #err; errOk err }}
```

- `listenerAt l a` := `isListener l` of a listener whose every accepted connection was dialed to an
  address serving the HTTP protocols (`lisProto la (httpReqP P a) (httpRespP P a)`) and its token `lisInv`.
- `handlerOk`/`servePre`/`serveDone`: `SpecPlan`'s. The `threadTok` in `servePre` is the connection
  goroutine's own (§0).
- `httpSrvEnv` (persistent): `httpEnv` plus what the server path reads that net/http's init does not
  yet prove (the bufio pools `wPool 2048`, `wPool 4096`, `rPool`, as `ServerConn.lean`; `time`, `log`,
  `context`). It is the premise until net/http's initialization is proved (phase 5 item 2).
- The CONNECT/hijack path stays as it is (`hijackOk`, `response.Hijack.spec`, net/rpc's
  `Server.ServeHTTP.spec`). `conn.serve`'s proof covers both kinds of address: a request on an HTTP
  address reaches `servePre`, and a `CONNECT` on an rpc address reaches `hjPre`. Question Q4 asks
  whether `Serve.spec_rpc` (dsverify's `RpcHttpServe`) should come out of the same proof.

**`expectContinueReader`.** Unreachable under the protocol: requests carry no `Expect`, and
`conn.serve` wraps the body only for `Expect: 100-continue`. Its proof would be the `canWriteContinue`
race with `writeContinueMu`. Skipped unless a client needs `Expect` (C3).

### 3. The chunked writer (`net/http/internal`, the client's request bodies)

The server's responses do not use it: `chunkWriter.Write` frames chunks itself. The Transport's
`transferWriter.writeBody` does, for a body of unknown length, which is rafthttp's snapshot.

```lean
/-- `cw` frames into the writer `wi` (an `io.Writer` contract over `Wr`, as `Spec/bufio/`'s
`bufio.Writer` specs take: `EtcdGrove.io.writerStream wi Wr`), having written the chunks `cs`
(non-empty) and not closed. -/
def chunkedW (cw : GoInterface) (wi : GoInterfaceOk) (Wr : List w8 → IProp GF)
    (cs : List (List w8)) : IProp GF := ...

abbrev NewChunkedWriter.spec : Prop := ∀ wi Wr,
  {{ writerStream wi Wr }} internal.NewChunkedWriter #(interface.ok wi)
  {{ (cw : GoInterface), RET #cw; chunkedW cw wi Wr [] }}
/-- `Write(p)`: one chunk of `p` (none if `p` is empty), its whole wire written through `wi`,
or an error with a prefix of the wire written. -/
abbrev chunkedWriter.Write.spec : Prop := ...
/-- `Close()`: the terminator `"0\r\n"` (the trailer and the final `"\r\n"` are the Transport's). -/
abbrev chunkedWriter.Close.spec : Prop := ...
```

Also `FlushAfterChunkWriter` (the Transport wraps the `bufio.Writer` when the body is chunked). Its
`Write` flushes after each chunk, which the snapshot's latency relies on, not the proof.

### 4. The client half (`transport.go`, `client.go`, `internal.ChunkedReader`)

**The Transport** (`transportOk t D`, persistent): a `*Transport` as etcd's `NewTimeoutTransport`
builds it. `Proxy` is `nil` or `ProxyFromEnvironment`, the scheme is `http` (TLS not used),
`DisableKeepAlives`/`MaxIdleConnsPerHost` are any. `DialContext` or `Dial` is a dialer `D` that
returns, for an address `a`, a `net.Conn` that is the net extension's (`isConn c cn false a`) or a
wrapper keeping its contract (etcd's `timeoutConn`). Its locks' invariants are `idleMu` (the idle
pool: each idle `persistConn` with its dialer-end tokens, between requests), `connsPerHostMu` and
`reqMu`.

```lean
/-- SpecPlan's `roundTripperOk` of the Transport: RoundTrip of a request built for `R` (`hreqOk R`)
to `R.host` serving `P`, with `□ P.hreq R τ`, its body contract, the ticket if `onceOnly`: an error
(`errOk`), or the response of one handler run: status, committed headers (`hdrView`), a body reader
of prefixes of what that handler wrote. -/
theorem Transport.roundTripperOk : transportOk t D ⊢ roundTripperOk (interface.mkOk (ptrT Transport) #t)
```

The proof is over upstream's `roundTrip`, `getConn` (the idle pool, `queueForIdleConn`,
`queueForDial`, `dialConnFor`, `wantConn`), `dialConn`, `persistConn.roundTrip`, `readLoop` and
`writeLoop` (both forked per connection, each with its own `threadTok`), `Request.write`,
`transferWriter`, `ReadResponse` (general heads, not only CONNECT's), `bodyEOFSignal`, and the retry
(`shouldRetryRequest`, `rewindBody`). HTTP/2, proxies and TLS stay `notModelled`. The protocol and the
premises below make them unreachable.

- **Response bodies:** `readerAt_read`/`readerAt_close`/`readerCloser` of `bodyEOFSignal` (its `Close`
  from another goroutine: the stream reader's `stop`). `Transport.CloseIdleConnections`.
- **`internal.NewChunkedReader`, `chunkedReader.Read`:** over a `bufio.ownReader` of a stream whose
  bytes are a prefix of `chunkedWire cs fin ++ trailer`. It yields a prefix of `cs.flatten`, and `EOF`
  only after the terminator. It is used on both sides: the server's request bodies (§2) and the
  client's chunked responses (rafthttp's stream reader).
- **`Client.Do`/`Client.Get`:** needed only by `xiang90/probing` (`rafthttp-gaps`, kaashoek's). A
  `Client{Transport: t}` with no redirects followed for a `GET` answered `2xx`/`4xx`: `roundTripperOk`
  plus `send`'s deadline plumbing. Q5 asks whether it is still needed.
- **The proxy environment (needs the user's sign-off, rule #8).** `ProxyFromEnvironment` calls
  `envProxyFunc()`, which calls `httpproxy.FromEnvironment()` once (`sync.Once`); that reads `os.Getenv`
  of `HTTP_PROXY`, `HTTPS_PROXY`, `NO_PROXY`, their lower-case forms and `REQUEST_METHOD`. With the four
  proxy variables (`HTTP_PROXY`, `http_proxy`, `HTTPS_PROXY`, `https_proxy`) empty, `proxyForURL` returns
  `nil` for every URL, whatever `NO_PROXY` and `REQUEST_METHOD` are (`httpproxy/proxy.go:127-145`), so
  the Transport dials `R.host` directly. That is
  coordinator-E's planned `proxyEnvOff` (#24, the grpc model's proxy finding). The proposal follows
  `envVerifyOff`'s pattern (`Spec/os/Getenv.lean`): a persistent token `envProxyOff`, given at program
  start under a per-machine pure premise `proxyEnvOff`, and a clause in `os.Getenv.spec`'s post:
  `envProxyOff -∗ ⌜key ∈ proxyEnvKeys → v = ""⌝` (`proxyEnvKeys` those four). The clause strengthens a trust-boundary axiom,
  by the same argument as `ETCD_VERIFY`'s: Go's `os.Getenv` reads the process's start environment, and
  nothing in the run sets these. `golang.org/x/net/http/httpproxy` is translated with its bodies
  (vendored in the toolchain).

### 5. Where this departs from `SpecPlan` (ledger entries before any edit)

- **C1 (simplification).** `Serve.spec` takes no `handlerPool`. The handler's `threadTok` is its
  connection goroutine's own, from Perennial's fork rule. `handlerPool_alloc.spec` becomes unused.
- **C2 (defect, `roundTripperOk`).** For a body of declared length (`NewRequest` of a
  `*bytes.Buffer`/`*bytes.Reader`/`*strings.Reader`: `ContentLength = n`), the Transport writes
  `Content-Length: n` before reading the body. The server's body reader returns `EOF` after `n` bytes
  and must then give `□ P.body R τ B`. But the client gets `Φb B` only from a later `Read` that returns
  `EOF`, after the last byte is already on the wire. So `roundTripperOk`'s body premise
  `□ ∀ B, Φb B -∗ P.body R τ B` cannot be used where it is needed. **Proposed:** `reqOwn r R bd` also
  records the declared length `cl : Option Nat` (`NewRequest` sets it), and for `cl = some n`
  `RoundTrip` asks `□ ∀ B, Preb B -∗ ⌜B.length = n⌝ -∗ P.body R τ B`. `NewBuffer_reader.spec`'s
  `Pre B := B <+: ys` gives it at `n = ys.length`. The main tree's `Boundary.lean` does not have this
  problem: its fixed body's bytes are `HReq.body`.
- **C3 (premise, `roundTripperOk`).** `hreqOk R`: `GET`/`POST`, a `reqPath`, a `host:port` host, header
  values the server's parser takes, and none of the Transport's own keys or `Expect`. rafthttp meets all
  of it. `Expect: 100-continue` would need `expectContinueReader` and the Transport's
  `ExpectContinueTimeout` path; nobody here sends it.
- **C4 (scope).** `protoAt` is the run's, not a generation's (`protoFam`, §0).
- **C5 (shape).** `readerAt`'s count is `uint.nat n` in `SpecPlan`. The model's readers return
  `0 ≤ n ≤ len(p)`, so the statement is unchanged; `sint` is not needed.

### 6. Questions (on #24)

- **Q1 (coordinator-E, dsverify-net):** take `SpecPlan`'s vocabulary for S5, as above, rather than
  `Boundary.lean`'s (`req`/`rhdr`/`streamed`/`sreq`, fixed bodies in `HReq`)? At S4, rafthttp's proofs
  would move from one to the other. Or keep `Boundary.lean`'s statements and define them over this?
- **Q2 (the user, via coordinator-E):** the `envProxyOff` token and the `os.Getenv` clause (§4).
- **Q3:** C2's change to `roundTripperOk`/`reqOwn`, and C3's `hreqOk` premise.
- **Q4 (dsverify-net):** should `conn.serve`'s proof also give net/rpc's `RpcHttpServe` instance (HTTP
  `Serve` on an rpc address, the handler `Server.ServeHTTP` through `muxHas`)? The loop is the same
  proof.
- **Q5 (kaashoek):** does `rafthttp-gaps`' prober still need `http.Client.Do`/`Get` over the Transport?
- **Q6 (S4):** what dialer contract does etcd's `rwTimeoutDialer.Dial`/`timeoutConn` need of `D`? The
  draft asks only that `D` return a connection with the net extension's `Read`/`Write`/`Close`/deadline
  specs.

**Order.** The vocabulary first (`Wire.lean`, the byte protocols, `protoAt`, `reserve`). Then the
server: `readRequest` on general heads, the body reader, the response writer, `conn.serve`, `Serve`.
Then the chunked writer and reader, then the Transport. Landed in batches, each on Lean's three
axioms, and no axiom added.

## For the user

1. **The deployment statement (S2/S4).** Decided 2026-11-22 (the user's answer, relayed by kaashoek on
   #24): one machine per member, over the net extension. The `net` half of the names-only swap goes to
   kaashoek's sessions once `phase7-dial` landed (it has, `bbc60799b2`); `net/http` stays here (S5).
2. **Stats handlers in the grpc model (S1):** kept (landed, `phase7-stats`). Open: the user's approval
   of the narrowed trusted claim (a handler sees a connection begin/end per stream; #24).

## Risks

- Goose and Perennial on the model's code: `mem.BufferSlice` and its pools, `sync.Cond`
  (`GracefulStop`), `time.AfterFunc`/`time.NewTimer`, `url.Parse` (targets), `fmt` verbs in
  `status.Errorf`, map iteration in header writing (specs must not fix header order), channels and
  `select` in the transport.
- The models' over-approximations may add error descriptions today's axioms exclude (REFUSED_STREAM,
  any non-OK code on a cut, idleness at any time, the spurious clean end of a server stream after a
  transparent retry, `nonissues/grpc-transparent-retry-spurious-eof.md`): proofs using `noRefusalAt`
  or `refusalDescs` must be rechecked.
- Addresses: `netAddrLit` is loopback-only (the `HTTP_PROXY` reason); the net extension's `addrOk`
  allows any unicast address. A distributed etcd over non-loopback addresses reopens rafthttp's
  `ProxyFromEnvironment` unless the deployment premise excludes a proxy environment.
- Size: option B's estimate, 60-110k Lean lines for all of it; dsverify's HTTP server proof alone is
  1.4k lines for a much simpler server.
