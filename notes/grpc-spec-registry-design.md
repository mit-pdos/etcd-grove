# gRPC spec registry: where service tables are fixed, and Grove's urpc compared (2026-11-27)

This note answers Upamanyu's feedback on the gRPC spec design: client and server should share a ghost resource that fixes the RPC specs before any machine steps, and handler code should be invisible to clients. It was written against `origin/lean` adc6c9ca2d. Grove sources: perennial @1e1acdf1bb, which is what grove-proofs' opam pins (`src/program_proof/grove_shared/urpc_{proof,spec}.v`), and grove-proofs @efb423a6d7. **[C]** marks what I checked in the source. **[I]** marks an inference.

## 1. Where and when each address's table is fixed

`grpcAddrAt a Svc := addrProto a (grpcCliPI Svc) (grpcSrvPI Svc) ∗ depSlotsCtx` (`InvGrpcWire.lean:488`). `Svc` is a parameter of the address's invariant `addrInvP` (`GooseLang/Ext/Net/Proto.lean:369,400`). It is set exactly once, from one of two resources, both exclusive:
- `addrUnset a`, through `grpc_addr_set` (`InvGrpcWire.lean:538`);
- `netAddrLeft a`, which `net.Listen` returns (`Spec/net/Listen.lean:37`), through `grpc_addr_set_tok` (`:550`).

Where each path fixes it **[C]**:
- **grpcdriver: in the initialization proof, after adequacy.**
  - `robust_of_distBootIT` (`grpcdriver/TopLevelRobustness.lean:47`) hands out `addrUnset drvAddr` (`:53`). It gets it from `addrs_start` (`Net/Statement/DistBridgeExts.lean:385,405`).
  - The proof then allocates `netProto_alloc`, `depSlots_alloc` and `γid` (`:54-56`) and sets the table `drvSvcG γid` (`:61`).
  - `Pl` gives the same fact to both boots (`:65-67,88-90,106-108`).
  - The table holds specs only (`Svc.lean:72-88,135`).
- **etcd/dist: in the initialization proof, after adequacy.**
  - `Net.robust_of_distBootILT` (`dist/TopLevelRobustness.lean:113`) hands out `addrUnset`.
  - `members_svc_start` (`ClusterStart.lean:176`; `server/ClusterStartD.lean:189`) then calls `etcdAddr_set` (`S2Interim.lean:121-129`, which wraps `grpc_addr_set`).
  - The table is `etcdSvc Γ mid`, an **interim axiom with no law** (`S2Interim.lean:72`). As a result, `Serve_dist` (`ServeDist.lean:69`) and the clientv3 contracts (`KVPutDist.lean`, …) are separate axioms.
- **etcd single-process (etcdstart, cluster3): at server start.**
  - `etcd_kv_started_with` (`client/v3/Results.lean:3567,3611`) goes through `grpcStartAtLis` (`:3510`) to `grpc.startCore` (`InvGrpcRun.lean:454`). `grpc.startCore` allocates the registry (`:472`) and sets the table from `netAddrLeft` (`:474`).
  - The table is Go's configuration, `grpcStartSvc` (`:252`). Its unary entries are `grpcGoEntry` (`InvGrpc.lean:227`): `∃ mh srv S, ⌜(name,mh,srv) ∈ regs⌝ ∗ □ grpcRunOkMd #mh srv ics S ∗ S md m Φ Ψe`. So **the table term names handler code and the registration list**.
  - Clients get registrations only from the server's proof: `grpc.serve` (`InvGrpcRun.lean:411`), called at `client/v3/Results.lean:2432` and elsewhere.
  - cluster3's bridges set `b`'s table from `netAddrLeft b` at the target's table (`etcdstart/Defs.lean:832-850`, `cluster3/StartBridge.lean:49`).

## 2. Do client-facing specs expose handler code, registrations or server state?

**At the gRPC level, no [C]:**
- `GrpcEntry` is `Wq`, `Wp` and `spec`; `GrpcStreamEntry` adds `up`, `dn` and `spec`. Neither has a `GoFunc` field (`InvGrpcWire.lean:433-457`).
- `isGrpcRpcMd` and `isGrpcStreamMd` are sealed (`@[no_expose]`), heap-free reads of the table: `∃ Svc Spec₀, grpcAddrAt a Svc ∗ ⌜Svc name = …⌝ ∗ □(Spec ==∗ Spec₀)` (`InvGrpc.lean:34`, `InvGrpcWire.lean:494-512`, `InvGrpcStream.lean:1469`).
- `Invoke`'s attempt (`grpcInvokerOk`, `InvGrpc.lean:755`) takes `isGrpcRpcsMd addrs method Spec` and the deposit `Spec md m Φ Ψe`. `NewStream` takes `isGrpcStreamsMd` (`ClientConn__NewStream.lean`). `NewClient` names no table (`NewClient.lean:40-50`).
- `grpcSrvNew` and `grpcServeTok` occur in `Spec/` only in server-side files: `NewServer`, `RegisterService`, `Serve`, the `Register*Server` files and `etcdstart/Serve`.

**At the etcd level, partly [C]:**
- The single-process spec instances that clients use name server state. Examples: `etcdPutSpecOn T E ρ cid mid` with `T := srvTLSId s`, a points-to on the server's config (`AuthReqDerive.lean:61`), and `E : apply.AEnv`, whose fields include `kv : GoInterface` and `f : GoFunc` (`apply/Chain.lean:688-694`).
- Through `grpcGoEntry`, the single-process table also names handlers. That term is hidden behind the sealed existential, so a client proof cannot use it **[I]**.
- The dist client contracts take only `etcdAddrAt`/`membersAt`, over the view `Γ` (`S2Interim.lean:88-98`).

## 3. Grove's urpc compared, and the shape for gRPC

**Grove [C].**
- `is_urpc_spec_pred Γsrv host rpcid Spec` (`urpc_proof.v:95-101`) is persistent. It holds a saved predicate transformer `Spec : list u8 → (list u8 → iProp) → iProp` for one `(host, rpcid)`, plus the host's invariant.
- The program's closed proof allocates it from adequacy's `host c↦ ∅` with `alloc_is_urpc_list_pred` (`:1143`). Example: `vrsm/apps/closed_proof.v:119-160`, where `grove_ffi_dist_adequacy` yields the channels and `alloc_vkv` follows.
- `wp_StartServer_pred` (`:413`) needs two things:
  - for each handler, `∃ Spec, is_urpc_spec_pred … ∗ is_urpc_handler_pred handler Spec`, where the handler predicate is `∀ req Post, {Spec req Post} f {Post rep}` (`:123-137`);
  - `handlers_complete`, so the handler domain equals the registered domain (`:276`).
- The client's `Client__Call` takes the fact and `□ ▷ Spec req Post` (`:1025-1031`). The record style (`RpcSpec` with `spec_Pre`/`spec_Post`, `urpc_spec.v:15-28`) is only sugar: `is_urpc_spec` is defined as `is_urpc_spec_pred (RpcSpec_Spec spec)`.

**This repository already has that shape, per address [C]:**

| Grove | here |
|---|---|
| `host c↦ ∅` from adequacy | `addrUnset a` from `addrs_start` (adequacy hands out nothing gRPC-specific: RULES #9 holds) |
| `alloc_is_urpc_list_pred` in the closed proof | `grpc_addr_set a Svc` in the program's initialization proof (grpcdriver, etcd/dist) |
| `is_urpc_spec_pred γ host rpcid Spec` | `isGrpcRpcMd a name Spec` (and `isGrpcStreamMd`); `Svc` is a Lean term in the address's invariant, not a saved predicate |
| `is_urpc_handler_pred f Spec` | `grpcRunOkMd #mh srv ics Spec` (`InvGrpcBase.lean:1111`): `∀ m Φ Ψe, {grpcSpecAt Spec ci m Φ Ψe ∗ …} mh … {Φ m' ∨ Ψe d}` |
| `wp_StartServer_pred` | `Serve` with `grpcServeTok gs lis a Svc ∋ grpcServes Svc …` (`InvGrpcRun.lean:149-176,216`): every entry is met by the handler `gs` registers under its name |
| `RpcSpec` record | none. `GrpcSpecMd := GrpcMd → Req.M → (Rep.M → IProp) → (GoString → IProp) → IProp` (`InvGrpcBase.lean:240`) is a transformer with the metadata and an error continuation added |

**Differences from Grove [C]:**
- The deposit is not persistent: one deposit, one run.
- There is no completeness condition: an entry with no handler gets `Unimplemented`, outside `handlerDescs`.
- Streams fit as a second entry kind (`GrpcStreamEntry`, with `grpcServesEnt`'s stream clause).

**Proposed shape: keep it, and make it the only route.**
- (a) Every deployment fixes `Svc a` (heap-free, built from ghost names it allocated first) in its initialization proof, right after adequacy, with `grpc_addr_set` from `addrUnset`. grpcdriver is the template.
- (b) `Serve` requires `grpcServes` (unchanged).
- (c) Clients get only `isGrpcRpcMd`/`isGrpcStreamMd` (unchanged).
- (d) etcd/dist replaces the axiom `etcdSvc` with a definition: an entry for each method at heap-free specs over `Γ` (the `etcdPutSpecOnW` family restated without `srvTLSId s`/`AEnv`). The KV*_dist contracts then become theorems from `Invoke` plus `grpcSvcAt_of_addr`, and `Serve_dist` a theorem from `Serve` plus `grpcServes (etcdSvc Γ mid)`.
- (e) `grpc_addr_set_tok` is left for bridges only, and the single-process server-start route retires with the single-process theorems (RULES #41).

**Trusted text:**
- `Serve`, `Invoke`, `NewStream`: no change for the registry.
- Start lemmas: theorems, so not trusted.
- `grpcAddrAt`: its meaning changes only at W5 (the opaques `grpcCliPI`/`grpcSrvPI` give way to the defined `grpcCliP`/`grpcSrvP`).
- Net trust change: −1 axiom (`etcdSvc`), then −`Serve_dist` and the 5 dist client axioms.

**The gap is therefore not in the gRPC interface [C+I]:**
1. Single-process etcd fixes its table at server start, from Go's configuration, which names handlers.
2. etcd/dist's table is an opaque axiom, because etcd's handler specs are not yet heap-free over the view (`S2Interim.lean:64`: "the entries' specs need S2's etcd side").

Adequacy stays minimal.

## 4. Impact on the stages

- **W1** (`NewServer`/`RegisterService` proved, `grpcSrvNew` defined with handler closures): **still applies.** `grpcSrvNew` is server-side only and corresponds to Grove's `own_Server s handlers` (`urpc_proof.v:212`). No client spec reaches it **[C, §2]**.
- **SW2** (the dec-shaped run contract, with the disjunction `grpcRunOkMd ∨ grpcRunPreOkMd`, `phase7-switch-dec:InvGrpcRun.lean:160`): **defer.**
  - Its content is how `Serve`'s model proof hands a handler its deposit (handlers start on the head, before data: plan-s2-endstate §1.1). It changes no client statement.
  - The model proof needs it only at W7.
  - The `Pre` arm exists only to keep `grpcGoEntry`. Land SW2 at W7 without that arm, after the single-process gRPC users are gone **[I]**.
- **W4** (single-process unary tables fixed at start): **moot under RULES #41** if the single-process gRPC theorems retire before W7. Its target shape (entries from a spec list, met by handlers) already matches the model, except that the table is fixed at server start.
- **W5** (protocols defined): **still applies**, and is independent of the registry. Its dependency changes from "W4" to "no `grpcGoEntry` users".
- **etcd adapters:** unchanged. `isGrpcRpc_leaseGrant_any` and the other conversions, and the `kVClient.*` specs, take only `isGrpcRpcsMd`.

**Recommendation.**
1. Tell Upamanyu the registry he describes already exists: the grpcdriver start fixes the per-address table after adequacy, `Serve` requires handlers to meet it as predicate transformers, and clients hold only sealed persistent facts.
2. Proceed with W1.
3. Shelve SW2 and W4.
4. Make the next gRPC/etcd item step (d): a defined `etcdSvc` over heap-free per-view specs, which retires `etcdSvc`, `Serve_dist` and the dist client axioms.
