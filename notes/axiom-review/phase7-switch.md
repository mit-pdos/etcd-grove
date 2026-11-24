# Review: phase 7's switch, SW1 (gRPC's trust boundary in end-state shape) (2026-11-24)

**Target.** The trusted text SW1 changes (branch `phase7-switch`; the plan `notes/phase7-endstate.md`
§1.2, as built §1.5 item 13, the two `NewStream` defects §2; ledger `notes/specs-only/ledger.md`,
2026-11-24). The axioms read against it: `grpc.Server.Serve.wp_proof`, `grpc.ClientConn.NewStream.wp_proof`,
`grpc.ClientConn.Invoke.wp_proof`, `grpc.NewClient.wp_proof`, `bridge.New.wp_proof`, `http.register`,
`etcd_noRefusal`, `etcd_noOtherRefusal`, and the opaque predicates beneath them (`grpcAddrAt`'s protocols
`grpcCliPI`/`grpcSrvPI`, `credsYieldRaw`, `grpcSrvNew`, `grpcSrvBound`).

**Reviewer.** An adversarial review by the `axiom` skill's method (read-only, no Go test and no Lean proof
built: every counterexample below is **inferred**), on `lean` `91ca351121`, the plan at `1a31ea2a3a`, and
SW1's worktree before its first commit. Its findings (the review's text is not in the repository) and
their resolutions follow.

## The trusted text, as SW1 leaves it

- **The service table** (`Proof/google_golang_org/grpc/InvGrpcWire.lean`, section `svc`): `ProtoWire`
  (with `cnt`, a `Pos.Countable` instance per model), `GrpcStreamEntry` (`Wq`, `Wp`, `up`, `dn`, `spec`),
  `GrpcSvcEntry` (`.unary`, `.stream`), `GrpcSvc`. An address's table is set once (`grpcAddrAt a Svc`,
  from `netAddrLeft a` by `grpc_addr_set`); the registrations are read off it: `grpcSvcAt` (unary),
  `grpcStreamSvcAt` (stream), and the client views `isGrpcRpcMd`, `isGrpcStreamMd`. `grpcReach`,
  `isGrpcStreamAt`, `grpcStreamServerAt` and `grpc.serveStream` are deleted.
- **What a server serves** (`InvGrpcRun.lean`): `grpcServes Svc ics sics regs sregs`, a clause per entry
  kind (`grpcServesEnt`): a unary entry names no stream registration and every unary registration of its
  name runs the entry's spec (`grpcRunOkMd`); a stream entry names no unary registration and every stream
  registration of its name converts the entry's `up₀`/`dn₀`/`spec₀` to and from its own `Up`/`Dns`/`Spec`
  and runs them (`grpcStreamRunOk`, which loses its `streamSpecOk` conjunct: the content family is given
  explicitly). `grpcServeTok gs lis a Svc` has one form for the server (no started disjunct, no server name
  `γ`): `grpcSrvNew gs … ∗ netListenerOpen lis a`, or the bound server `grpcSrvBound gs lis a …` (below),
  with `grpcAddrAt a Svc` and `grpcServes Svc …`. `Server.Serve.spec`'s text is unchanged.
- **The single-process start** is a theorem (`grpc.start'`, `grpc.startBound`, over `grpc.startCore`):
  Go's configuration as a table (`grpcStartSvc`: `grpcGoSvc`'s unary entries, then the stream list `sms`).
- **The attempt's metadata** over an `IProp` (`InvGrpc.lean`): `opaque credsYieldRaw conn cm : IProp GF`
  (was the opaque `Prop` `credsYield`), `credsYieldI := □ credsYieldRaw`, `grpcAttemptMdI`, `connCredsOk`
  over `credsYieldI conn cm -∗ …`; `NewClient`'s `perRPCCredsOk` gains `credKeysOk cm` (no metadata key
  starting with `':'`); client/v3's `clientAttemptMdI`.
- **The client end of a stream** (`InvGrpcStream.lean`): `cliStreamIs cs γ Req Rep Up Md Dn cd Ok`, the
  dispatch family `Md a md` and the content `Dn a md` indexed by the dispatch; `RecvMsg`'s message arm
  returns `∃ a md, Md a md ∗ streamDispIs γ a md ∗ … ∗ Dn a md L.length m`. `streamDispIs γ a md`
  (`InvGrpcCall.lean`): a discarded ghost variable at `γ.md` holding the address and a finite code of the
  metadata (`GrpcMdCode`), persistent, with `streamDispIs_agree`.
- **`NewStream`** (`Spec/google_golang_org/grpc/ClientConn__NewStream.lean`): one client content `Up` for
  every address (the registration at `fun _ => Up`); the post fixes neither address nor metadata:
  `cliStreamIs … Up (fun a md => ⌜a ∈ addrs⌝ ∗ clientAttemptMdI conn om md) Dn …` and
  `□ ∀ a md, ⌜a ∈ addrs⌝ -∗ clientAttemptMdI conn om md -∗ Spec a md γ (Dn a md)`.
- **`bridge.New`** (`Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/New.lean`): takes
  `grpcAddrAt a Svc ∗ grpcAddrAt addr Svc` at one `Svc` (no longer `netAddrLeft a`; the caller spent it
  setting `a`'s table to the target's) and returns no `grpcAddrIs` wand.
- **`http.register`** (`Proof/net/http/Axioms.lean`) also consumes `netAddrLeft a`.
- **`etcd_noRefusal`, `etcd_noOtherRefusal`** (`v3rpc/NoRefusal.lean`) return `grpcSrvBound gs lis addr …`
  in place of `grpcSrvNew gs … ∗ netListenerAt lis addr`.
- **Deleted**: the axioms `grpc.start`, `grpcAddrIsRaw`, `grpcSrvCfgRaw`, `grpcSrvLink`, and
  `grpcAddrIs_agree`, `grpcSrvCfg_agree` with them (nothing reads a server name).
  **Added**: the axiom `grpcSrvBound` and the opaque `credsYieldRaw` (replacing the opaque `credsYield`).

## The findings and their resolution

1. **Unsound, already on `lean`: `noRefusalAt` survives replacing the server at the address.**
   `etcd_noRefusal` gave `grpcSrvNew gs … ∗ netListenerAt lis addr` back beside `⌜noRefusalAt addr⌝`, a fact
   about the address string; `grpcServeTok` tied neither `gs` nor `lis` to the certified server. A program
   could take the certificate, drop `gs`, build `gs2` whose KV `Range` returns the learner refusal (a
   handler that always errors meets every unary spec), serve it on `lis`, and a client panicking on the
   refusal is proved safe by `grpcInvokerOk`. (A second route: a later listener at `addr` serving the same
   table with other handlers.)
   **Resolved (interim):** both axioms return `grpcSrvBound gs lis addr …` (a new axiomatized exclusive
   predicate), which only `grpc.startBound` consumes and `grpcServeTok` holds as its bound form of the
   server at the listener: the server `Serve` runs at `addr` is the one certified. The second route needs
   the listener back, which nothing returns. End state: decision E's table form (no-refusal a property of
   the unary entries, checked by `grpcServes`, read by `grpcInvokerOk` from `grpcSvcAt`), which retires
   `grpcSrvBound`.
2. **A transparent retry can move a stream to another address** (`getTransportConn`, the model's
   `modelChooseAddr`, `model_clientconn.go:322`): a post fixing `a` when `NewStream` returns is true only
   with a prophecy, and §1.4's call protocol could not prove it. **Resolved:** the address is learned with
   the responses as the metadata is (`streamDispIs γ a md`), `Up` is one for every address, and the post is
   `□ ∀ a md, …` at `Dn a md` (§1.5 item 13). The watch client learns member and token from the first
   response of each epoch (`epochAt`, `respcE`; ledger 2026-11-24, "the watch and lease clients' stream
   specs"); the lease client takes an existential dispatch family and never reads the content.
3. **`bridge.New` against §1.4's per-connection slots** (a justification gap for W5, no exploit: the
   bridge's post exposes no ghost state). **Recorded, not changed in SW1:** `notes/phase7-endstate.md`
   §1.4, "Bridges against per-connection slots": S3.1 keys the slot and its refusal by the call `γ`, or adds
   a relay law (`depSlot_relay`), before the bridge's axiom is read against the defined protocols.
4. **An HTTP server and a grpc table at one address** (unsound at W5): `http.register` took only the
   listener, so a program could serve HTTP at `a` and set `a`'s grpc table. **Resolved:** `http.register`
   consumes `netAddrLeft a` (commit `0953893924`).
5. **R1 is not a defect of the Lean text** (`cliStreamIs`' error arm `cliStreamErr` already admits a bare
   `io.EOF`). **Resolved:** §2 restates R1 as SpecPlan's defect only; `cliStreamIs`' `io.EOF` arm keeps
   `downClosed γ L` as it was.
6. **Cosmetic.** `credsYieldRaw` carries `hG` (`include hG`), which its definition over `grpcConn`'s ghost
   state will need; `ProtoMsg.cnt` is not a global instance (the `*.msgCountable` instances are local to the
   message modules); `GrpcMdCode` represents only finite metadata, which a dispatched one always is (built
   from the head's fields). `InvGrpcCall.lean`'s docstring no longer says the server learns the dispatch
   from its run's context (no interim statement gives it).

## What survived (by reading)

One table per address (`netPend a ∅` exclusive; no equation between the opaque protocols of two tables;
entries not forgeable without the setter's `grpcAddrAt`); the bridge (one `Svc` term at both addresses);
one dispatch per attempt (transparent retry only of an unprocessed first attempt; no retry policy); no
reply without the handler (v1.84's cardinality checks); R2's fix (`spec₀` holds at every `γ`;
`streamDispIs_agree` ties later responses to the first); the attempt's metadata (`createHeaderFields`:
credentials then `om`, pseudo-headers skipped, `ValidatePair`, `-bin` round trip); `credKeysOk` needed
(`ValidateKey` accepts `':'`-keys, `pathOf` takes the last `:path`); every grpc-made error satisfies
`clientErr`/`statusErrOk` and none is a handler description; routing (C3 and its mirror blocked by the
kind clauses; full method names injective; unflagged stream descriptors excluded by `RegisterService`'s
premise). Not tried: per-namespace address spaces of distributed deployments, and SW2's `grpcDecDepOk`
beyond the one-`D` argument.

## Verdict

**Survives after the fixes** (findings 1, 2, 4 applied in SW1; 3 a recorded obligation of S3.1; 5, 6
text). The user's review of SW1's trusted text is pending.

**Trust base** (`etc/tcb-report.py --check` on the VM's full build of `phase7-switch`, 2026-11-24): the
axioms `grpc.start`, `grpcAddrIsRaw`, `grpcSrvCfgRaw`, `grpcSrvLink` gone, `grpcSrvBound` new (in every
collection that starts an etcd member under `etcd_noRefusal`/`etcd_noOtherRefusal`); leaseexpiryN's
collection gains `rand.Int63n.wp_proof`, `v3rpc.pbWatchRequestT_reg`, `v3rpc.pbWatchResponseT_reg`, all
already in the trust base (inferred, not traced: its members' start now runs the Watch stream's server
proof, `GetProgressReportInterval`'s jitter, through `grpc.start'`'s stream list).
