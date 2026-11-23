# `putget_safe`: one member machine, one client machine (plan and status)

2026-11-23. Branch `putget-dist` (off `net-swap` `9d69145b8d`; merge `lean` once `net-swap` lands). The
first distributed etcd theorem: the interim form of `etcd_safe` (`notes/etcd-dist-plan.md`, Q7: no machine
crashes, over Perennial's `goose_dist_adequacy`) cut down to one member and one client, and without
`Remote` (the client machine runs the check itself).

Files:

- Go: `examples/etcd/dist/putget/` (`putget.go`: `Member`, `Client`; `cmd/{member,client}`;
  `putget_test.go`: `TestPutGet`);
- translation: project `putget-dist` of `etc/goose.py` (packages `examples/etcd/dist/{putget,env}`);
  `Proof/.../examples/etcd/dist/{putget,env}/{Base,Init}.lean`, `putget/{InitLinked,PkgTable}.lean`
  (`etc/gen-init.py`: a root and a `PROGRAMS` entry);
- the statement: `Spec/.../examples/etcd/dist/putget/TopLevelRobustness.lean` (`putget_safe.spec`), its
  definitions `Proof/.../examples/etcd/dist/putget/TopLevelDefs.lean`;
- the proof skeleton: `Proof/.../examples/etcd/dist/putget/TopLevelRobustness.lean` (section 5).

## 1. The two programs

**The member machine**: `putget.Member(peer, client)`: `env.ClearProxy()`, then
`etcdstart.StartServer("putgetd", peer, client, zap.NewNop())` (the one member of a new cluster, token
`putgetd`: `NewServer`, `Start`), `etcdstart.Serve(s, client)` (`v3rpc.Server`, `net.Listen`, `go
gs.Serve(l)`), then `holdForever` (a `time.Sleep` loop). An error from a step returns.

**The client machine**: `putget.Client(ep)`: `env.ClearProxy()`, `etcdstart.NewClient(ep, zap.NewNop())`, a
`Put` of `k` with `v` and a `Get` of `k`, each in a context with the examples' request timeout, and a panic
unless the `Get`'s first key-value has `v`. An error from any step returns `false` without a check (the dist
rules, `examples/etcd/dist/client`'s package doc: a failed `Put` is an unknown outcome).

These are the in-process driver `examples/etcd/putget`'s two halves, each on a machine of its own, so that
every step has a proved spec today (`etcdstart.StartServer`, `Serve`, `NewClient`, `clientv3`'s `Put`/`Get`)
and the existing proof `Proof/.../examples/etcd/putget/Main.lean` splits into the two machines' proofs.

**Layout, and why not `examples/etcd/dist/server`.** The plan's layout puts `etcd_safe`'s programs in
`examples/etcd/dist/{server,client}` with `cmd/`; a single-machine workload stays one machine (§2). `putget_safe`
gets a package of its own beside them, `examples/etcd/dist/putget`, with its own `cmd/member` and
`cmd/client`, because:

- `dist/server`'s `Main` serves etcd's full peer handler (`etcdhttp.NewPeerHandler`, Q8: untranslated;
  `http.Server.Serve` on it is phase 7 S5) and builds its `ServerConfig` itself, where `etcdstart`'s
  `StartServer` has a proved spec. With one member, nothing dials the peer address, so the member needs no
  peer handler. When D2 translates `dist/server`, `putget_safe` can move onto it (one more spec: the
  configuration `serverConfig` builds is `etcdstart.cfgOk`'s);
- `dist/client`'s `RunPutGet` does 50 rounds under a key prefix and needs `AwaitCluster` (a loop of reads)
  and the whole `client` package (every workload, `remote`): translating it is D2. `putget.Client` is one
  round, as the in-process proof.

`dist/client`'s `RunPutGet` is unchanged (it is `etcd_safe`'s putget workload).

**The test** (`TestPutGet`, `DIST_RUN=1`, as `TestDist`; `-short`: one faulty round): one member machine and
one client machine on network namespaces (`examples/lib/robust`; rerun in a user namespace or by sudo when
needed, the local mode otherwise), the member's data directory and WAL area linked to empty directories of its
own, the member started, then (a liveness wait of the test only: the member's client address accepts a TCP
connection from the client's machine) the client. Round 0 has no fault and must check; rounds 1-4
(`PUTGET_ROUNDS`) run a `robust.NetNemesis` from the client's start (partitions, one-way partitions, link
faults; no crash). Run 2026-11-23 (this machine, container root, the bridge variant): round 0 checked; faulty
rounds 3 of 4 checked, one ended (6 partitions, the `Put` timed out); no panic, no member exit.

## 2. The statement

```lean
def putget_safe.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (peer client : GoString)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : etcdstart.BootFacts id ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcdstart.premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) name peer client n id ctxs
          boot)
    (HNs : prometheus.namesUnclaimed (bootMember peer client) putget.initNames ∧
      prometheus.namesUnclaimed (bootClient client) putget.initNames)
    (σm σc : state) (g : GlobalState) (Hm : MemberFiles σm)
    (Hd : Net.DistDeploy (addrs peer client) (system peer client σm σc) g),
    Robust [] (system peer client σm σc) g (threads := 2 ^ 28) (bound := 2 ^ 40 - 11)
```

over the extensions `etcdNetExts := ⟨[idIssueExt, Fs.fsExt, Net.netExt]⟩` with the file extension at
`etcdFsSem` (`TopLevelDefs.lean`; the plan's option (i) bundle), `system peer client σm σc :=
[(bootMember peer client, σm), (bootClient client, σc)]`, each boot program `putget.initialize' #()` then the
function applied to the addresses' Go strings, `addrs peer client := [peer, client]`, and `MemberFiles σm`
the single-process `etcdWalAreasInit` for the member's directory on its own machine. Shape: `etcd_robust.spec`'s
(the draft) with one member and one client and no crash list; the premises are the in-process `putget`'s
`Main.spec`'s and the retired single-process `etcd_safe`'s per-cluster ones (`Hprem`, `Hctx`, `Hcec`, `HNs`).
Dropped against those: `addrsUnclaimed`/`dataDirsAbsent`/`verifyEnvOff` (each machine's network and files are
its own: `DistDeploy`, `MemberFiles`, and `ClearProxy`), `v3rpc.ServerMethodSets` and `errors.AsTarget` (the
retired theorem discharged them from the package assumptions; the proof will too).

**Builds** (2026-11-23, against Perennial `9c3b81f30`; section 6). Not yet `putget_safe` itself: the
skeleton's `putget_safe_of_boot` (section 5).

## 3. Dependencies: what exists, what is a placeholder, what is missing

| Piece | State |
|---|---|
| The two programs' translation, `Init`/`InitLinked`/`PkgTable` | **done** (`putget-dist`; the closure is the in-process `putget`'s plus `env`) |
| The bridge for `etcdNetExts` with every machine stable: `DistBootWpG` per machine to `Robust []` | **missing, provable** (no axiom): `robust_of_distBootRB`'s proof over a three-extension bundle: a `GooseGpreS putgetGF` instance (`AllG` at slot 0 for all three, as the retired `etcdGF`), the three extensions' init predicates (`extsInitgP`/`extsInitP`), the projections of `extsGlobalStart` onto the net extension's (`net_globalStart`'s) and of `extsLocalStart` onto the file extension's (`etcdFsExts_localStart`'s). The skeleton takes it as `PutgetBridge` |
| `isPkgInit putget` on each machine | **exists**: `InitLinked`'s `wp_initialize'` and `PkgTable` (generated), as the counter's boot |
| The member's boot WP up to `Serve` | **exists as the in-process `Main.wp_proof`'s first half** (`StartServer`, `Serve`, `alloc1`, `kv_served`), given the member's start resources below |
| `env.ClearProxy`'s spec | **missing (Perennial model)**: `os.Unsetenv` is names-only in Perennial's translation (`Perennial/Code/os.lean`); its spec needs the environment as machine-local state (`examples/etcd/dist/env`'s TODO; upamanyus's U-extra on #24). Then `ClearProxy` gives `envVerifyOff` (what the start axiom gives today). A callee hypothesis `env.ClearProxy.spec` until then |
| The member's start resources: `dataDirFresh`, `netAddrFree client` (= `addrClaim client ∗ netLisTok client`), `prometheus.nameFree` of the closure's metric names, `envVerifyOff`, `threadTok` | **placeholder**: in one process `goose_adequacy_start` (an axiom, `Proof/runtime/Start.lean`) hands them out; nothing hands them out on a machine of a distributed start. `netLisTok client` comes from the net library's start (`addrUnset`, `DistBridge`); `addrClaim` is an axiomatized token whose only source is that axiom (`netAddrFree`'s design D); `dataDirFresh` is an axiomatized token (`WalDir.lean`) whose definition from `MemberFiles` and the file extension's start (`etcdFs_start`'s `osTree`) is the WAL link's (`notes/wal-link-scope.md`); `nameFree` is `prom-registry`'s (the default registry on the Go heap: provable at the machine's initialization). A named hypothesis (`MemberStart`) of the skeleton; **no new axiom** |
| The member's named Iris premises (`etcdstart.premises`), `Hctx`, `Hcec` | premises of the statement, as in the single-process theorems |
| The cluster's ghost state | **exists, in the member's proof**: with one member, `alloc1` runs inside the member machine's WP (as `Main` does); nothing of it is shared but what the client's calls need (below). D7's global/local split is not needed for one member |
| **The client's calls reaching the member's server across machines** | **blocked on phase 7 S2** (section 4) |
| The client's WP | **exists as the in-process `Main.wp_proof`'s second half** (`NewClient`, `putGetInv_alloc_log`, `client_Put_own`, `client_Get_own`, the check), given the member's KV registrations at the client's own ghost-state instance: exactly what does not exist across machines |

## 4. The gRPC statement needed across machines

**What the client's proof consumes today.** `client.client_Put_own`/`client_Get_own` (and `NewClient`'s
`srvWEnv`) take `client.kvRegsAt ⟨addr, E, γr, cid, mid⟩` = `isGrpcRpc addr "/etcdserverpb.KV/Put" (etcdPutSpec
E γr cid mid) ∗ isGrpcRpcMd addr ".../Range" (etcdRangeSpecE …) ∗ …`, which `etcdstart.Serve`'s spec produces
on the member (`etcdKVAt`, `etcdKVAt_regs`), and the client's `ClientConn.Invoke` axiom consumes. By definition
(`Proof/google_golang_org/grpc/InvGrpc.lean`):

```lean
isGrpcRpcMd addr name Spec := ∃ γ, grpcAddrIs addr γ ∗ isGrpcRpcAt γ name Spec
isGrpcRpcAt γ name Spec := ∃ c mh srv, grpcSrvCfg γ c ∗ ⌜(name, mh, srv) ∈ c.regs⌝ ∗
  □ grpcRunOkMd #mh srv c.ics Spec     -- the handler's WP, at the caller's HeapGS
```

`grpcRunOkMd` is a Hoare triple of `methodHandlerCall mh srv …`: the member's handler `mh` on the member's
server value `srv`, **at the heap of whoever holds the fact** (the definitions' section variable `hG`). In one
process it is the same heap; across machines the client's `Invoke` needs it at the client machine's `HeapGS`,
where `srv` and everything the handler reads are not allocated.

**No interim form over the existing axioms is sound across machines.** The only way to give the client
`isGrpcRpcMd` at its heap from the member's is a transfer law, `isGrpcRpcMd (hG := hGm) addr name Spec ⊢
isGrpcRpcMd (hG := hGc) addr name Spec` for two instances sharing the global ghost state, which would have to be
a new axiom, and it is false: it gives the client machine a WP of the member's handler on the client's own heap,
and a client program may call that handler itself (the function table is global, `[GoGlobalContext]`) on a
location it does not own; the WP says the call is safe where it is stuck. Not added. (As a hypothesis of an
intermediate theorem it would make the theorem vacuous; the skeleton does not take it.)

**What S2 has to give** (the statement the client's proof needs; its server half from the member's handlers):

1. a **heap-independent registration** of a method at an address, say `grpcSvcAt addr name Spec`
   (persistent, over the global ghost state only: no `HeapGS`), in the net protocol library's address registry
   (`regCtx`, `addrs_set_proto`, as `remote`'s `svcAddr` sets `reqP`/`repP` of a service: `Net/.../remote/
   Robust.lean`, `remote_start`): set at the deployment's start with a service chosen later, or published by
   `grpc.Server.Serve` through a saved predicate at a name the start fixes;
2. **the server side**: `grpc.Server.Serve` on a listener at `addr` whose configuration registers `(name, mh,
   srv)` with `□ grpcRunOkMd #mh srv ics Spec` on the server's own heap (what `Serve`'s callers prove today)
   makes `grpcSvcAt addr name Spec` true (the transport's `acceptRun` runs the handler on the server machine);
3. **the client side**: `ClientConn.Invoke` on a connection to `[addr]` takes `grpcSvcAt addr name Spec` where
   it takes `isGrpcRpcMd addr name Spec` today, with the same pre and post (`Spec md m Φ Ψe` consumed once per
   attempt, `Φ` of the reply on success, an error in `clientErrTys` with the caller's `Ψe` otherwise), so that
   `isGrpcRpc` can be **redefined** as `grpcSvcAt` (or as `∃ γ, grpcAddrIs addr γ ∗ grpcSvcAt …`) and
   clientv3's specs and proofs keep their statements;
4. `Spec`'s predicates stay over `GF`: the client never runs them, it only passes them along (etcd's specs
   mention the member's apply environment `E : apply.AEnv GF`, whose `IProp` fields the member defines at its
   own heap; ghost ownership is global, so the client may hold and return them). `ProtoMsg`'s `send` is
   heap-dependent but only `M` (the pure model) crosses: `GrpcSpecMd Req Rep` must be read at `Req.M`/`Rep.M`.

With (1)-(3), `putget_safe`'s missing piece is the rendezvous: the start fixes the client address's service as
"etcd's KV calls at whatever apply environment the member publishes", the member publishes `E`, `ρ`, `cid`,
`mid` and the client's `putGetInv` (allocated from the member's initial KV state, `Hetcd`) after `Serve`, and
the client reads them. Before the member publishes, there is no listener at `addr` (the member has not reached
`Serve`'s `Listen`), so a dial is refused and the client ends without a check: the net extension's semantics
says so, and S2's `Invoke` must let the client's proof use it (a call that succeeds implies a published service).

**Blocked on phase 7 S2**: yes, for the client machine's WP and for the member's server side across machines.
Everything else of the closed proof is either done (translation, init), provable now (the bridge, the member's
boot up to `Serve`), or a start resource with no source in a distributed start (section 3), which is the same
question for every distributed etcd theorem (D2/S4).

### Question for upamanyus (#24; draft, not posted)

> putget_safe (one etcd member machine, one client machine, no crash; `notes/putget-dist-plan.md` on branch
> `putget-dist`) is stated and builds. Its client machine's proof is the in-process putget's client half and
> needs, across machines, what `isGrpcRpcMd addr name Spec` gives in one process. Today `isGrpcRpcAt` holds
> `□ grpcRunOkMd #mh srv ics Spec`, a WP of the server's handler at the caller's own heap, so the client machine
> cannot hold it (and a transfer between heaps would be unsound: a client could call the handler itself on an
> unallocated location). Three questions for S2:
>
> 1. Will S2's `ClientConn.Invoke` take a heap-independent registration (`grpcSvcAt addr name Spec` over the
>    global ghost state, e.g. in the net library's address registry as `remote`'s `svcAddr`), with
>    `grpc.Server.Serve` making it from the handlers' `grpcRunOkMd` on the server's own heap? If so, can
>    `isGrpcRpc`/`isGrpcRpcMd` be redefined as that, so clientv3's specs (`client_Put_own`, `kvRegsAt`, ...)
>    keep their statements?
> 2. Who fixes an address's service: the deployment's start (protocols set at `addrUnset`, the service chosen
>    later, as `remote_start`), or `Serve` at run time (a saved predicate at a name the start allocates)? etcd's
>    specs depend on the member's apply environment `E`, known only once the member has built its server, so
>    the start can only fix "the service the member publishes".
> 3. Before the server publishes, a dial to `addr` is refused (no listener). Will `Invoke`'s spec let the
>    caller conclude, from a success, that the service is published (so that the client's proof needs no
>    ordering between machines)?
>
> Interim, putget_safe's skeleton takes the client machine's boot WP as a hypothesis of an intermediate theorem
> and adds no axiom. Is there anything in S2's draft signatures we should state the skeleton against now?

## 4b. Other gaps found (no Go bug)

- The member's start resources (section 3) are the same question for every distributed etcd theorem: the
  single-process start axiom `goose_adequacy_start` hands out `addrClaim`, `dataDirFresh`, `nameFree`,
  `envVerifyOff`; a distributed start has no such axiom, and none is added here. For S4.
- No bug in the verified Go code was found.

## 5. The proof skeleton

`Proof/.../examples/etcd/dist/putget/TopLevelRobustness.lean`:

- `PutgetBridge` (a `Prop`, the bridge's statement for `etcdNetExts` at `putgetGF`: `robust_of_distBootRB`'s);
  provable now (section 3), not yet proved;
- `putget_safe_of_boot`: `putget_safe.spec` from `PutgetBridge` and `PutgetBoot`, the start update from the
  two addresses unset to a share per machine with each boot program safe from its share (`BootWp`: `Net.DistBootWpG` for `etcdNetExts`), at the
  statement's premises. **Proved** (it is the bridge applied to the statement's premises);
- `PutgetBoot` is where the member's boot WP and the client's boot WP go: the member's needs `MemberStart`
  (section 3) and `env.ClearProxy.spec`; the client's needs S2's statement (section 4). Neither machine's WP is
  proved yet: their in-process halves are `Main.wp_proof`'s, to be split once the client's precondition has
  S2's shape (stating the client's triple over today's `kvRegsAt` would fix a precondition no distributed proof
  can meet).

## 6. Checks (2026-11-23)

- `go vet ./etcd/dist/...`, `go test ./etcd/dist/...` (in `examples/`), `DIST_RUN=1 go test -run TestPutGet
  ./etcd/dist/putget/`: pass (section 1).
- `etc/goose.py --check --project putget-dist`: up to date; `etc/gen-init.py --check`: 270 files up to date;
  `etc/tier-check.py --check`: ok (no new violation; the skeleton is a linking module).
- `lake build` (through the build slot, `--packages=/shared/tmp/manifest-9c3b.json`) of
  `Proof.../dist/putget.{TopLevelRobustness,PkgTable,InitLinked}` (and so the statement): completed, 4460 jobs.
