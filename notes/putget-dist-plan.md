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
skeleton's `putget_safe_of_boot` (section 5). The bound is `2 ^ 28 - 1` and each machine's `FsInit` is a premise
(`MemberFiles`, `ClientFiles`): section 7, "Two findings".

## 3. Dependencies: what exists, what is a placeholder, what is missing

| Piece | State |
|---|---|
| The two programs' translation, `Init`/`InitLinked`/`PkgTable` | **done** (`putget-dist`; the closure is the in-process `putget`'s plus `env`) |
| The bridge for `etcdNetExts` with every machine stable | **proved** (2026-11-23): `Net.robust_of_distBootI` over any list of extensions with the net extension (section 5) |
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

- `putget_safe_of_boot (HS : PutgetBoot) : putget_safe.spec`, **proved** from the all-stable bridge over
  `etcdNetExts`, `Net.robust_of_distBootI` (`Net/Statement/DistBridgeExts.lean`, proved, no axiom: over any list
  of extensions with the net extension; `DistBridge.lean`'s theorems are its corollaries), with each machine's
  `FsInit` from the statement (`etcdNetExts_initP`, `TopLevelDefs.lean`) and `putgetGF`'s `GooseGpreS`;
- `PutgetBoot`: the start update from the two addresses unset to a share per machine, each machine's boot
  program safe from its share and its whole start (`DistBootWpS`: local start resources, thread token, bounds).
  Its split into the start, the member's and the client's boot is section 7.

## 6. Checks (2026-11-23)

- `go vet ./etcd/dist/...`, `go test ./etcd/dist/...` (in `examples/`), `DIST_RUN=1 go test -run TestPutGet
  ./etcd/dist/putget/`: pass (section 1).
- `etc/goose.py --check --project putget-dist`: up to date; `etc/gen-init.py --check`: 270 files up to date;
  `etc/tier-check.py --check`: ok (no new violation; the skeleton is a linking module).
- `lake build` (through the build slot, `--packages=/shared/tmp/manifest-9c3b.json`) of
  `Proof.../dist/putget.{TopLevelRobustness,PkgTable,InitLinked}` (and so the statement): completed, 4460 jobs.

## 7. The member's distributed start (design, 2026-11-23; with upamanyus's S2 answer on #24, 04:16Z)

**What exists now (proved, this branch).** `Net/Statement/DistBridgeExts.lean`: the all-stable bridge over any
list of extensions with the net extension, `robust_of_distBootI` (`DistBridge.lean`'s net-only theorems are now
its corollaries at `netExts`, statements unchanged; kvnet's #22 `NetFsBridge.lean` untouched). A machine's
obligation is `DistBootWpS bound e σ P`: from its share `P`, **its extensions' local start resources**
(`extsLocalStart σ.world`: its files' `osStart`, its listeners), no package initialized, **the main thread's
token** `threadTok`, and the logic's bounds (`receiptBound ≤ bound`, `threadBound = receiptBound + 1`), its
boot program is safe. So of the five resources the single-process `goose_adequacy_start` gives
(`startRights Ns Ds` = `nameFree` of `Ns`, `dataDirFresh` of `Ds`, `envVerifyOff`; plus `threadTok`), and the
address claim `addrClaim` that `netAddrFree` still holds after net-swap:

| Resource | Single process (after net-swap) | Distributed start (this design) |
|---|---|---|
| `threadTok` | `goose_adequacy_start`'s `Hwp` | **given**: `DistBootWpS` (each machine's main thread; `nodeWpBody`'s) |
| `netLisTok a` (in `netAddrFree a`) | the net extension's start | **given**: the deployment's `addrUnset a` (`addrs_start`), in the start update's input |
| `addrClaim a` (in `netAddrFree a`) | nothing since net-swap (the retired theorems' start gave it) | **goes at S2**: it is the closed-world claim the grpc axioms (`grpc.start`) rest on; S2's per-address service registration (`grpcSvcAt`, set once by `Serve` from the start's right) is that claim, proved over the net extension. Until S2: a hypothesis of the member's boot (`MemberStart`), never an axiom |
| the per-address service right, `γE` (upamanyus, point 2) | — | **the start update allocates them** for the member's client address: the right to set its service once (from `addrUnset client`, as `addrs_set_proto`), and a one-shot agreement name `γE` for the member's apply environment; the member's share gets the right, both shares get `γE` |
| `dataDirFresh (memberDataDir name)`, `memberAreasFresh` | `startRights`'s `Ds` (axiomatized token `dataDirFresh`, `WalDir.lean`); `memberAreasFresh` allocated from the member's `fsExt` root (`WalAreas.lean`) | **from the machine's own files**: `MemberFiles σm` (`FsInit` and `etcdWalAreasInit` of the member's directory) with `extsLocalStart`'s `osStart` (`etcdFs_start`): `memberAreasFresh` as `WalAreas.lean` does today; `dataDirFresh` once it is a definition over the tree (the WAL link, `notes/wal-link-scope.md`), until then a hypothesis |
| `prometheus.nameFree` of the closure's names | `startRights`'s `Ns` | **gone** with `prom-registry` (the default registry on the machine's own heap); until it lands, a hypothesis |
| `envVerifyOff` | `startRights` | **from the program**: `env.ClearProxy`'s spec, once `os.Unsetenv` has a model (`notes/perennial-changes.md`, 2026-11-23); until then `env.ClearProxy.spec` is a callee hypothesis |

So after S2, prom-registry and the WAL link, the member's start needs nothing beyond `NetStart` (no
connection: `DistDeploy`), `ServerStart` (`MemberFiles`: its files as on disk, its directory empty) and the
start update's allocations (the service right and `γE`); no start axiom for distributed theorems.

**The skeleton's shape** (`PutgetBoot`, `Proof/.../dist/putget/TopLevelRobustness.lean`) splits, once S2's
signatures are posted (`phase7-s2`, `notes/phase7-plan.md`), into:

```lean
-- the start update (provable once S2's start lemma exists): the two addresses unset ⇒ γE,
-- the member's share (the client address's service right, γE), the client's share (γE)
PutgetStart : ∀ [G], ⊢ addrUnset peer ∗ addrUnset client ={⊤}=∗
  ∃ γE, memberShare client γE ∗ clientShare client γE
-- the member's boot: StartServer, Serve (which sets grpcSvcAt client name (Spec E) and envAt γE E), hold
MemberBoot : MemberStart (addrClaim client until S2, dataDirFresh, nameFree, ClearProxy's spec) →
  DistBootWpS bound (bootMember peer client) σm (memberShare client γE)
-- the client's boot: NewClient, Put, Get (each success returning envAt γE E and the reply's Φ under Spec E)
ClientBoot : DistBootWpS bound (bootClient client) σc (clientShare client γE)
```

where the client's knowledge is `∃ E, envAt γE E ∗ …` (point 2) and `isGrpcRpc` is S2's redefinition
(`grpcSvcAt` plus the address's agreement), so the client's proof is the in-process `Main.wp_proof`'s second
half with `client.kvRegsAt` read from `envAt`. These names (`grpcSvcAt`, `envAt`, the service right) are
upamanyus's; nothing here defines or axiomatizes them before his signatures are posted. The client's
`putGetInv` (allocated in-process from the member's initial KV state, `Hetcd`) is the member's to allocate
before `Serve` and publish with `E` (a field of what `envAt γE` agrees on, or a second one-shot name): a
question for S2's signatures.

**The member's boot up to `Serve` against these resources** is the in-process `Main.wp_proof`'s first half
(`StartServer`, `Serve`, `alloc1`, `kv_served`) with `memberStartRes name ⟨none, some client⟩` from the table
above, then `holdForever` (a `time.Sleep` loop: a WP with any postcondition). Not written yet: it needs
`putget.Member`'s own spec file (callees `env.ClearProxy`, `StartServer`, `Serve`, `holdForever`) and, for the
part after `Serve`, S2's `Serve` (which publishes the service); written against today's `Serve.spec` it would
end with `etcdKVAt` on the member's heap, which S2 replaces.

**Two findings of this step.**
- **`Fs.fsSemWithS` keeps `ExtSemantics`'s default `initLocal`** (any state), unlike `Fs.fs_semantics`
  (`FsInit`, since 2026-11-22): so `Robust` over `etcdFsSem` does not give a machine's files as on disk, and
  `GooseInitCompat` fails for the file extension at `etcdFsSem`. `putget_safe` takes `FsInit` per machine as a
  premise (`MemberFiles`, `ClientFiles`), and the bridge takes the initial-state conditions as a hypothesis
  (`robust_of_distBootI`). The fix is `initLocal st _ := FsInit st` in `fsSemWithS` (a trusted-semantics change,
  with its example: not made here).
- **The step bound** is `2 ^ 28 - 1` (was `2 ^ 40 - 11` in the first statement): `goose_dist_adequacy` bounds
  threads over every execution of `n` steps, which the bridge meets with `n + 2`, and the server's specs take
  `threadBound ≤ 2 ^ 28`. An along-the-execution distributed adequacy (as the single-process
  `goose_adequacy_below`) would restore it (`notes/perennial-changes.md`, 2026-11-23).

## 8. Against S2's draft signatures (2026-11-23; `notes/phase7-plan.md` on `phase7-s2-design` `0606f68248`, §"S2 draft signatures")

Supersedes section 7's sketch of `PutgetStart`/`MemberBoot`/`ClientBoot` (written against the first answer:
there is no saved predicate of the service, the agreement is on a view, `envAt` reaches the client through
`etcdPubSpec`'s `Φ`).

**The placeholder** (`Proof/.../examples/etcd/dist/putget/S2Draft.lean`, a defs module; marked PLACEHOLDER):
his pure types `ProtoWire`, `GrpcEntry`, `GrpcSvc` verbatim, and the rest as the fields of one structure
`S2Draft` (no axiom, no `opaque`), with his names and statements: `depSlotsCtx`/`depSlots_alloc`,
`grpcAddrAt`, `grpc_addr_set` (spends `addrUnset a`), `EnvView`, `etcdEnvOf`, `viewRd`, `envPubTok`, `envAt`,
`envPub_alloc`, `envPubInv`, `etcdSvc`, `kvRegsPub`, `kvRegsPub_at` (at the client's own heap). Two fields are
our reading of his §1.3 start (marked): `envPubInv_alloc` (the token split into the invariant's half and the
member's, `envPubHalf`) and `kvRegsPub_of_addr` (the clients' `kvRegsPub` from the address set at `etcdSvc`:
`grpcSvcAt_of_addr` with the redefined `isGrpcRpcMd`). When his branch lands, each field becomes his
definition or theorem and the structure goes.

**The skeleton** (`Proof/.../TopLevelRobustness.lean`), all proved, no axiom, no `sorry`:
- `putget_start` (**proved** from `S2Draft`'s fields): his start, steps 1-4: the slot map, `γE`, the
  publication invariant at the member's `Pub`, the client address set to `etcdSvc γE cid mid`; the member's
  share `memberShare` (`grpcAddrAt client (etcdSvc …)`, its half of the token, `envPubInv`) and the client's
  `clientShare` (`kvRegsPub client γE cid mid`, `envPubInv`). The peer address's `addrUnset` is dropped
  (nothing listens there).
- `putget_safe_of_s2 (HS2 : ∀ [GoGlobalContext], S2Holds) (HB : PutgetBootS2) : putget_safe.spec`
  (**proved**): the net library's registry (`netProto_alloc`), `putget_start`, the bridge
  (`putget_safe_of_boot`). Its hypotheses: `S2Holds` (S2's names exist, at every global ghost state:
  `Nonempty (S2Draft putgetGF)`) and `PutgetBootS2` (`BootsS2`: the cluster id `cid` the table is fixed
  at, and under S2's names, the member's `Pub` and each machine's `DistBootWpS` from its share at every `γE`).
  `#print axioms`: Lean's three and five axiomatized predicates of the statement's and clientv3's vocabulary
  (`dataDirFresh`, `envVerifyOffTok`, `prometheus.nameUnclaimed`; `grpcAddrIsRaw`, `grpcSrvCfgRaw` through
  `client.kvRegsAt`, which S2's redefinition of `isGrpcRpcMd` removes).

What is left for `putget_safe`: `S2Holds` (S2), the member's boot from `memberShare` and section 7's start
resources (publishing `envAt γE ν` with `□ Pub ν`, his `env_publish`), the client's boot from `clientShare`
(its first call at the `etcdPubSpec` form, then `kvRegsPub_at`), and the cluster id (`cid`: bootstrap's,
fixed before the machines run since the table is a Lean term; a question for us: `BootFacts` gives the
member id, not the cluster id).

**From putget's side, on his open questions.**
- **O1 (the view).** putget's client calls `Put` and `Range`, auth off: `etcdPutSpec`, `etcdRangeSpecE`,
  `putReplied`, `rangeReplyOk`, `rangeErrReply`, `srvLogCert`, `revMinted`
  (`Proof/go_etcd_io/etcd/client/v3/KVService.lean`, `server/v3/etcdserver/InvRequest.lean`). Of `AEnv` they
  read `E.γs` (`srvApi.kvLogLb`), `E.γrev` (`revTok`, in `revMinted`), `E.authOn` (`putReplied`), and two
  predicate fields: `E.Nx` (`□ E.Nx log`, in `srvLogCert` and `rangeErrReply`) and `E.Cp` (`□ E.Cp crev`, in
  `rangeErrReply`); and the read names `γr` (`viewRd ν`). So the view needs `γs`, `γrev`, the auth mode and
  the read names, and `Nx` and `Cp` must be definitions over names in `etcdEnvOf ν` (or saved predicates over
  `mvcc.Log` and `Int`, as O1 says). Which they are on the member is the member's construction (`srvEnv`,
  `env₀`): to check with him.
- **O2 (no heap in the table).** putget is auth off, so the auth-on specs (`etcdPutSpecOn s E …`) are not in
  putget's table: O2's suspect case does not block us. But `#check @client.etcdPutSpec` and
  `@client.etcdRangeSpecE` (auth off) still show `[hG : HeapGS HasLC.hasLC GF]` (with `[go.Semantics]`): the
  conjunct that uses it is to be found (candidates: `kvOpAu1`/`kvReadAu`'s atomic updates, the receipts `⧖`,
  `revTok`). If it is only a section variable that the definitions use through a ghost-only conjunct, the
  table's entry can be stated at any heap; if not, that conjunct moves to the server's run contract.
- **O3** (`tree` into `ProtoMsg`): nothing on putget's side (its messages are `pbPutRequest`/`Response`,
  `pbRangeRequest`/`Response`).

### 8b. After upamanyus's reply (#24, 05:09Z): `cid`, O1, O2

- **`cid` is in the view.** `S2Draft.viewCid : EnvView → w64`; `etcdSvc γE mid` and `kvRegsPub a γE mid` no
  longer take it, and `kvRegsPub_at` gives `client.kvRegsAt ⟨a, etcdEnvOf ν, viewRd ν, viewCid ν, mid⟩`.
  `BootsS2` lost its `∃ cid`.
- **O1: `Nx` and `Cp` are determined by names.** The started member's environment (`NewServerR.lean:1514`,
  the record every server proof builds) has
  - `Nx := srvApi.kvNx ρ.rd false`, where `kvNx γr on log := ∃ A, srvRLogLb γr.raft A ∗ ⌜kvModelM on γr.kv A =
    log ∧ mvcc.LogPutsLe etcdKeyMax log⌝` (`KVStoreApi.lean:62`), and `srvRLogLb γ L := isCommittedLogLb
    γ.raft.cl (srvLE γ L) ∗ ⌜srvIdxOkW γ.ai0 L⌝` (`SrvRaftLog.lean:395`): ghost lower bounds at the read names
    `ρ.rd` (`raft`, `kv`) and the auth flag;
  - `Cp := kvCpOk ρ.rd.kv`, where `kvCpOk γk c := (⌜c = -1⌝ ∨ kvCmpPermit γk c) ∗ ⌜γk.cmp = false → c = -1⌝`
    (`InvRequest.lean:1267`) and `kvCmpPermit γk c := ⌜0 < c⌝ ∗ kvRevLbZ γk (c + γk.cret)` (`:1261`): ghost, at
    the KV names `ρ.rd.kv`.

  So both are Lean functions of `ρ.rd` (and a boolean): `etcdEnvOf ν` can set `Nx := srvApi.kvNx (viewRd ν)
  false`, `Cp := kvCpOk (viewRd ν).kv`; no saved predicate is needed for them. (The pre-start record
  `etcdstart.env₀`, `Defs.lean:212`, has `Nx` a parameter and `Cp := True`; the client-facing specs see the
  started one.)
- **O2: where `HeapGS` comes from.** `#check` shows `[hG : HeapGS]` on `etcdPutSpec`, `etcdRangeSpecE` and every
  conjunct they use (`putReplied`, `srvLogCert`, `rangeReplyOk`, `rangeErrReply`, `srvApi.kvLogLb`, `kvOpAu1`,
  `kvReadAu`, `kvRevLb`, `revMinted`, `revTok`, `appliedWit`, `committedAtLeast`). `#print` with explicit
  arguments shows the bodies reach it only as `hG.goose_globalGS.gooseAllG` (the universal camera, in the
  global ghost state: `srvApi.kvLogLb` is `monoListLbOwn (GooseGlobalGS.gooseAllG hG.goose_globalGS) …`), plus,
  for the specs, through `[go.Semantics]` (an instance over the heap's Go local context). Checked by `rfl`:
  at any two `HeapGS` with the same global part and the same Go local context, `etcdPutSpec … o Φ` and
  `etcdRangeSpecE … md o Φ Ψe` are definitionally equal (scratch file, 2026-11-23). So beside the message
  models in the types (`pbPutRequest` etc., his O3), the specs depend on a machine only through its Go local
  context, which `Robust`'s `Fresh` makes the same `lctx` on every machine: they can be stated at `⟨G, L⟩` for
  any `L` with `goose_go_local_context = lctx` (as `putgetHeapAt`), or re-sectioned over `[GooseGlobalGS]` and
  `[GoLocalContext]`.

## 9. Merged with `lean` (net-swap landed, `82847d941b`, Perennial `70706ce5e`); what can land

The branch merged `lean` cleanly; `etc/goose.py --check --project putget-dist` is up to date at Perennial
`70706ce5e`; `etc/gen-init.py` regenerated putget's `PkgTable` (the new pin's package list); the putget targets,
`DistBridgeExts` and its users (`DistBridge`, `NetFsBridge`, remote's counter, echo) build
(`manifest-7070`).

**The bundle is shared now**: `etcdNetExts` (with its semantics, interpretation, `HasExt` instances and
`etcdNetExts_initP`) moved from putget's `TopLevelDefs` to `Proof/.../examples/lib/etcdstart/NetExts.lean`,
beside `etcdFsExts` (`FsExts.lean`), listed importable in `etc/api/etcdstart.txt`: the place for any etcd program
over `[idIssueExt, fsExt at etcdFsSem, netExt]`, distributed or single-process (`single-process-restore` can
import it instead of defining its own). Its ghost bundle stays per theorem (`putgetGF`; a single-process theorem
needs its own `GooseGpreS`).

**Recommendation: land this branch as it is** (its pieces stand on their own; a separate branch would only
split commits that are already separate):
- `Net/Statement/DistBridgeExts.lean` (`robust_of_distBootI`, `robust_of_distBootE`, `DistBootWpS`) with
  `DistBridge.lean`'s theorems as its corollaries (statements unchanged): no axiom, no trust-base change
  (`counter_remote_robust`: Lean's three);
- `etcdstart/NetExts.lean` (above);
- `examples/etcd/dist/putget` (Go, `TestPutGet`), project `putget-dist`, its `Init`/`InitLinked`/`PkgTable`;
- `putget_safe.spec` (Spec) and `TopLevelDefs`, and the skeleton (`putget_safe_of_boot`, `putget_start`,
  `putget_safe_of_s2`), all proved from named hypotheses.

**`S2Draft` does not block**: it is a definition in our defs module (a `structure` and three pure types), no
`axiom`, no `opaque`, nothing outside `examples/etcd/dist/putget` imports it, and it appears only as a
hypothesis (`S2Holds`) of `putget_safe_of_s2`. The trust-base reports see no new axiom: no root is closed (no
`putget_safe` theorem yet), and the skeleton is a linking module under `Proof/` (tier check ok). What to watch at
the gates: `etc/tcb-report.py --check` (no `Link`/`Results` of ours, so no new root), the interface of
`etcdstart/NetExts` (generated, committed), `etc/api-check.py etc/api/etcdstart.txt --check`.

## 10. The member's boot, proved against S2's draft (2026-11-23, branch `putget-boot`)

`putget_safe_of_s2` now takes only the **client** half as a boot hypothesis: the member machine's boot is
proved (`member_boot`, `Proof/.../dist/putget/AdequacyMember.lean`) from `S2Holds` and four named hypotheses
(`MemberBootHyps`), no axiom, no `sorry`.

**What is proved.**
- `Member.wp_proof` (`Proof/.../dist/putget/Member.lean`, spec `Spec/.../dist/putget/Member.lean`):
  `env.ClearProxy` (callee spec, gives `envVerifyOff`), `zap.NewNop`, the member's start bundle
  (`etcdstart.memberStartRes_one`), `StartServer` from the named premises (`etcdstart.wp_StartServer1`,
  new in `etcdstart/StartOne.lean`, **shared with the in-process `Main.wp_proof`**, which now uses it in
  place of its own copy of the glue: `bootPremise_of`, `commonPremises`, `alloc1`, the one-member directory),
  the client's putget invariant from the bootstrap log's KV state, `Serve` in S2's form (`S2Draft.Serve_s2`),
  publishing the view with `Pub`, then `holdForever` (`holdForever.wp_proof`, a `time.Sleep` loop).
- `member_boot`: `DistBootWpSL srvLevelK (2^28-1) (bootMember peer client) σm (memberShare S client γE id
  (putgetPub S))`: the file extension's start on a machine of `etcdNetExts` (`etcdNetFs_start`, new in
  `etcdstart/NetExts.lean`), the member's WAL area from `MemberFiles` (`wp_walAreas`), `putget`'s
  `wp_initialize'`, `Member.wp_proof` at its linked callees.
- `Pub` is fixed: `putgetPub S ν := ∃ γf, ∀ L, client.putGetInv (hG := heapAt G L lctx) (viewRd ν) γf k v`
  (`Defs.lean`): the client's invariant at every local ghost state over the global one (it reads only the
  global part, `putGetInv_heap`, by `rfl`). The member's obligation on `Pub` is `memberPubOk`.
- `memberShare`/`clientShare` moved from `TopLevelRobustness` to the defs module `Defs.lean`.

**`S2Draft.Serve_s2` (PLACEHOLDER, this skeleton's statement of his §3 prose).** At the member's heap: from
`memberUp s ρ E₀ lg γn mid` (the started member, its id `mid` = the table's), today's `Serve.spec` premises
(logger, method sets, quota, bounds, plus `grpcRepliesFit`, `srvLevels`, `receiptBound ≤ 2^48`, which today's
caller-side `kv_served` takes), `grpcAddrAt a (etcdSvc γE mid) ∗ envPubHalf γE ∗ envPubInv γE Pub` and the
caller's `∀ ν, ⌜viewRd ν = ρ.rd⌝ ={⊤}=∗ □ Pub ν`: an error, or `∃ ν, envAt γE ν ∗ ⌜viewRd ν = ρ.rd⌝`.
Taking the whole `memberUp` (not its parts) is what ties the table's `mid` to the server's member id; to
check with upamanyus.

**The receipt floor.** `Serve` needs `srvLevels` (`srvLevelK ≤ threadBound`), which `DistBootWpS` (receipts
`≤ bound` only) cannot give for short executions. `Net/Statement/DistBridgeExts.lean` gains
`DistBootWpSL lo bound` and `robust_of_distBootIL` (an execution of `n` steps run at `max (n+1) lo`
receipts); `robust_of_distBootI` is its floor-0 corollary (statement unchanged). `PutgetBoot` and the boots
now use the floor `srvLevelK`, and `PutgetBoot` takes the addresses' `addrOk` (from `DistDeploy`).

**The named hypotheses (`MemberBootHyps`), each with no source yet on a distributed machine:**
- `clearProxy`: `dist_env.ClearProxy.spec` (`Spec/.../dist/env/ClearProxy.lean`, no proof file) — needs an
  `os.Unsetenv` model with the environment as machine-local state (Perennial change, not made);
- `names`: `⊢ prometheus.namesFree initNames` — until `prom-registry` (registry on the machine's heap);
- `dataDir`: `⊢ dataDirFresh (memberDataDir name)` — until `dataDirFresh` is a definition over the machine's
  file tree (WAL link; blocked on the fs redesign, #15). Consistent: no axiom says `nameFree`/`dataDirFresh`
  is exclusive (`Start.lean`'s satisfiability argument);
- `peerPlain`: `addrOk a = true → types.plainPeerURL ("http://" ++ a)` — a pure fact, provable, not yet done.

**What remains for `putget_safe`:** `S2Holds` (S2, including `Serve_s2`), `MemberBootHyps`, and the client
half `PutgetClientS2` (`ClientBootS2`: `DistBootWpSL srvLevelK _ (bootClient client) σc (clientShare S client
γE id (putgetPub S))`): the in-process second half over S2's `Invoke`; `NewClient`'s `srvWEnv` names the
member's watch server state `R` (heap-dependent), which S2's `NewClient`/view must replace; the view comes
from the first call's `etcdPubSpec` reply, then `kvRegsPub_at` and `putgetPub` (opened at the client's heap)
give `kvRegsAt` and the putget invariant. The client also needs `names` for its own initializer and
`plainEndpoint client`.
