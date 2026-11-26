# The `_dist` trust-boundary specs against the in-process specs they copy (mechanical diff)

2026-11-26, worktree `etcd-safe-f7` @ `d3c3a29b87` (#50, the lead's request). Read-only: no build, no proof.

**Final texts (2026-11-26, `etcd-safe-f7` @ `eb138f6f8c`, F7 step 3, the lead's option (a)).** The replacement is made:
`NewServer.specG_dist` is the proposed text below plus `etcdURLsFit U.peer → etcdURLsFit U.client →` (after `peerURLsDir`,
as in-process), `Serve_dist.spec` is the proposed text (the old one deleted), `AuthServeProposed.lean` is deleted, and
`StartMember_dist` has `addrFits peerAddr → addrFits client →` back and the post `memberUpL … lm γl` (new binder `γl`).
All three items of the summary below are resolved:
1. resolved: `specG_dist` takes `etcdURLsFit` (MainLogger discharges it from the deployment's `addrOk`,
   `etcd_dist.addrOk_addrFits`, `etcdstart.etcdURLsFit_httpURL`); its header lists every change and no longer says the rest
   is verbatim except them.
2. resolved: `StartMember_dist` takes `addrFits` again (putgetK's member discharges it from `memberShareK`'s `addrOk`).
   New, recorded in its header: its post `memberUpL … lm γl` is stronger than what `StartMember` can be proved to meet at
   putgetK's names (no lessor slot: putgetK's start passes `ClusterNames.lsNone`); it is a hypothesis (`HSM`), no axiom.
3. resolved: `Serve_dist` ties `Γ.ls mid`, `Γ.kv.lm` and (auth on) `Γ.au mid`; `etc/lease-order-check.py` passes.
The two doc nits are fixed (the `specGAt` sentence is now "the lessor part is proved in one process"; the
distinct-names sentence says only the auth one is kept, the lessor's stays a premise of the four lease axioms), and
the `Hsdo` comment is the in-process text. The sections below keep the pre-replacement comparison; "PROPOSED"
now means the text the axiom has.

**Summary (before the replacement): UNJUSTIFIED / suspicious.**
1. UNJUSTIFIED: `NewServer.specG_dist` (and the proposed `specG_dist_proposed`) drop `etcdURLsFit U.peer → etcdURLsFit U.client →`, and the header says "nothing else". Decided: carry them into the replacement. The other `StartMember_dist` drop is item 2.
2. UNJUSTIFIED (placeholder, not an axiom): `StartMember_dist` drops `addrFits peerAddr → addrFits client →`, the premise that discharges item 1 at the boot, and its "What changes" list does not mention it.
3. Suspicious, known (F2 review, `f2-lease-axioms.md`): the current `Serve_dist` serves `memberUp` at lease mode `.none` (the default) and does not tie `Γ.ls mid`. The proposed text fixes both, and the lease axioms are unlinked.

Everything else either adds premises or weakens the post (both conservative), or replaces the in-process network or registration by its counterpart over the net extension. Each such difference is justified below.
No in-process counterpart: `NewPeerHandler_dist` (etcdhttp is names-only, with no spec). `PeerServe_dist` is compared with
`http.Serve_ok`'s `Serve_spec` (the docstring's reference).

Method: each statement cut out of its file, `--`/`/- -/` comments stripped, whitespace normalised, split at
top-level `→`/`∗`, the client names renamed (`isKv kv γ dup`/`kvClientAt …` → one token, `Γ.kv` → `γ`, `api` → `kv`,
`□?dup` dropped), then `diff`. Helper: `/shared/tmp/f7diff/norm.py` (not in the repo).

Recurring differences, justified once (referred to as R1-R5 below):
- **R1** `[π : NetProtoGS]` binder added: the statements are over the net extension's protocol names.
- **R2** `isKv kv γ dup` → `kvClientAt cl api eps V Γ` (`New`'s client, `clientNoProxy`, its `KV` field, `membersAt eps Γ`).
  `isKvOf`'s three facts become:
  - `kvSame x.γr.kv γ` → the address facts at `Γ`: `etcdSvc`'s intended interpretation is `kvCongr` with `Γ.kv`
    (`Serve_dist`'s premise), and `kvCongr` implies `kvSame`;
  - `dup = false → noRefusalAt` → `Γ.auth = false`: `etcd_noRefusal`'s premise is `E.authOn = false`;
  - `receiptBound GF ≤ 2^62` dropped: on another machine the server's receipt bound is the server machine's
    (`Serve_dist`'s `[ReceiptBoundLe GF (2^48)]`), not the client's.
- **R3** `dup := false`, so the AU is no longer under `□?dup`: auth off (the premise `Γ.auth = false`) means a write is
  sent at most once. Read-only AUs stay `□`, as in-process.
- **R4** The error arm loses `kvErr err` (lease calls: `clientErr err`, `statusErrOk err`): the post is weaker,
  and nothing is claimed of a remote error.
- **R5** `levelTok 0 ∗ (…)` → `levelTok 0 ∗ …`: parenthesisation only.

## `NewServer.specG_dist` (`NewServer_dist`) ↔ `NewServer.specG`
Counterpart: `Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean:151`. Dist: `Spec/…/etcd/dist/NewServerDist.lean`.

| difference | kind | justification |
|---|---|---|
| `[π : Net.NetProtoGS]` | binder added | R1 |
| `(γn : NetNames GF)` | binder → post `∃ γn` | the cross-machine network is the peer addresses'. The post fixes `γn.N = srvNet γ ∧ γn.dir = dir`, as the premise `%Hγn` did. Justified |
| `etcdURLsFit U.peer → etcdURLsFit U.client →` | **premises dropped** | **UNJUSTIFIED**: fmt stage 1 (c486fbb43f) added them for `publishV3`'s and the transport's `strings.Join`s, which run on a member machine too. The header's "nothing else, the rest is its text verbatim" is false. Lead's decision: carry them into the replacement, discharged at the start from `addrFits` and one URL per member |
| `"#Hnet" ∷ netHttpOk γn id` | premise replaced | → `"#Hpeers"`: `httpAddrAt γ pid a` for each other voter `pid ∈ γ.vs` and each of its directory addresses. This is the in-process streams' registry and `pipeReg` of every other member, restated over the net extension (`netHttpOk` ranges over the directory's members, `#Hpeers` over `γ.vs`; `rafthttp.bootCfg dir γ.vs` makes these the same set). Justified |
| `"%Hγn" ∷ ⌜γn.N = srvNet γ ∧ γn.dir = dir⌝` | premise → post | see the `γn` row |
| `"#Hnoproxy" ∷ noProxyEnv` | premise added | the program checks the environment. In-process, the transport never dials over the net, so no proxy can intervene. Justified (and conservative) |
| post `∃ γn …, ⌜γn.N = srvNet γ ∧ γn.dir = dir ∧ …⌝` | post: `γn` existential | see the `γn` row |

No other difference: every other premise and post conjunct is token-identical. Only comments differ, at `Hsdo`, whose
comment is stale in the dist file.

## PROPOSED (now the axiom's, plus `etcdURLsFit`) `NewServer.specG_dist_proposed` ↔ `NewServer.specG` (and ↔ the then-current `specG_dist`)
Proposed text: `Proof/…/etcd/dist/AuthServeProposed.lean:104` (deleted; now `Spec/…/etcd/dist/NewServerDist.lean`, with
`Hlslot`/`Hγa` last in the precondition and `etcdURLsFit` carried). Compared with the current `specG_dist`, it has exactly the intended additions:

| difference | kind | justification |
|---|---|---|
| `(γa : auth.AuthNames)` | binder added | P-A1: the start allocates the member's auth names (`Γ.au mid`). Intended |
| `(γl : GName)` | binder added | P-L1: the start chooses the lessor name (`Γ.ls mid`). Intended |
| `"Hlslot" ∷ (ghostMapAuth γl ½ ∅ ∗ lease.lessorSlot γl)` | premise added | token-identical to in-process `NewServer.specGAt`'s `Hlslot` (F7 step 2), only moved last. Intended |
| `"Hγa" ∷ (if on then authNamesFreshD γa else True)` | premise added | the fresh authorities that `NewServer` allocates today are handed in. Intended |
| post `(on = true → ∃ γa, E.authMode = .on γa)` → `(on = true → E.authMode = .on γa)` | post strengthened | tied to the binder by `Hγa`. Intended |
| post `∧ mvcc.api.mvccLeases E.γ = γl` | post added | token-identical to `specGAt`'s post. Intended |

Compared with `NewServer.specG`, it has every difference of `specG_dist` above, the `etcdURLsFit` drop included (**UNJUSTIFIED**, to be
carried), plus the rows of this table. Compared with `specGAt`, the lessor part is identical. Doc nit: the docstring's "the in-process
`NewServer.specG` is not yet carried to the name" is stale now that `specGAt` exists (d3c3a29b87).

## `Serve_dist` ↔ `etcdstart.Serve.spec`
Counterpart: `Spec/…/examples/lib/etcdstart/Serve.lean:52`. Dist: `Spec/…/etcd/dist/ServeDist.lean`. The shapes
differ: the in-process spec takes the caller's ghost step and gives `Q`; the dist one serves `etcdSvc Γ mid` at `a`.

| difference | kind | justification |
|---|---|---|
| `[ThreadBoundLe GF (2^28)]` vs pure `threadBound GF ≤ 2^28` | premise restated | equivalent |
| `[ReceiptBoundLe GF (2^48)]`, `[π]` | premises added | the server machine's receipt bound (see R2); R1 |
| `zapLoggerOk cfg.Logger'`, `cfg.TracerOptions' = nil`, `WatchProgressNotifyInterval' = 0`, `isServerReqM`, `isServerReadM`, `srvAuthLb`, `srvServeFacts`, `srvWatchBuilt`, `srvLgReader`, `srvBemuReader`, `srvGoRes` | premises → packaged | in `zapLoggerOk lg ∗ memberUp s ρ E₀ lg γn mid` (`cfg.Logger' = lg`; the auth-off views and `srvAuthLb` come from `serveViews_off`, as the in-process auth-off callers get them). Justified |
| `E.authMode ≠ .any` | premise → derived | `serveViews_off` gives it from `memberUp`. Justified |
| `netAddrFree addr` | premise replaced | → `etcdAddrAt a Γ mid`: the start set the address (`etcdAddr_set` spends `addrUnset a`), and `addrProto` gives the right to listen. Justified |
| caller's ghost step `∀ gs lis cid mid R, grpcUpM … ={⊤}=∗ (∃ Svc, grpcServeTok …) ∗ Q …` | premise dropped | the service is fixed to `etcdSvc Γ mid` by the address fact. No caller-chosen `Svc`/`Q`. Justified |
| `grpcRepliesFit`, `srvLevels` | premises added | in-process, the callers' ghost steps take them (the `StartMember`/`Main` premises of `cluster3`, `txnlin`, …). Conservative |
| `kvCongr ρ.rd.kv Γ.kv ∧ Γ.auth = false` | premises added | tie the view to the member: KV names congruent with `Γ.kv`, auth off matching `memberUp`. Justified |
| post `err ≠ nil ∨ (nil ∗ Q …)` → `True` | post weakened | conservative |
| `memberUp … mid` at its default lease mode `.none`; nothing ties `Γ.ls mid` | missing tie | **Suspicious, known** (F2 review: `Lease_LeasesGranted_dist` with `Lease_Grant_dist` UNSOUND today; unlinked). `kvCongr` ties `ρ.rd.kv.lm = Γ.kv.lm`, but nothing ties the member's lessor mode or name to `Γ`. Fixed by the proposal |

## PROPOSED (now the axiom's) `Serve_dist_proposed.spec` ↔ `etcdstart.Serve.spec` (and ↔ the then-current `Serve_dist`)
Proposed text: `AuthServeProposed.lean:283` (deleted; now `Spec/…/etcd/dist/ServeDist.lean`, verbatim). It differs from the current `Serve_dist` in exactly these rows:

| difference | kind | justification |
|---|---|---|
| `(Γ.auth = true → ∀ a b, Γ.au a = Γ.au b → a = b) →` | premise added | distinct auth names, guarded to auth-on views (re-review C's N2). Redundant given the tie. Conservative |
| `Γ.auth = false` → `Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist` | premise generalised | `kvCongr` omits `hist`. With auth on, every member's history is the cluster's (`kvCongrOn`). Intended |
| `memberUp …` → `if Γ.auth then memberUpOnL … (Γ.au mid) Γ.kv.lm (Γ.ls mid) else memberUpL … Γ.kv.lm (Γ.ls mid)` | premise replaced | ties the auth names, the lessor name and the lease mode to the view (fixes summary item 3). `memberUpL` is `memberUp` verbatim plus `mvccLeases E.γ = γl`. `memberUpOnL` is `memberUpOn` verbatim plus that conjunct (no `srvStopRight`, as in `memberUpOn`). Intended |

Compared with `Serve.spec` with auth on: `memberUpOnL` gives `isServerReqM true`, `isServerReadM true`, `srvAuthLb` and
`E.authMode = .on γa ≠ .any`, which is what `Serve.spec` takes at `E.authOn = true`. The rest is as in the previous section. Doc nit: "the
drafts' distinct-names premises (kept here too)" covers only the auth one here. Lessor distinctness stays a premise of the four lease axioms.

## `StartMember_dist` ↔ `etcdstart.StartMember.spec` (placeholder hypothesis, no axiom)
Counterpart: `Spec/…/examples/lib/etcdstart/StartMember.lean:33`.

| difference | kind | justification |
|---|---|---|
| `[π]`, `(S5 : S5Draft GF)` | binders added | R1, plus S5's names |
| `(γn : NetNames GF)`, `γn.N = srvNet γ →`, `γn.dir = dir →` | dropped → post `∃ γn` | as in `NewServer_dist`. Listed in the header |
| `addrFits peerAddr → addrFits client →` | **premises dropped** | **UNJUSTIFIED**, not in the header's "What changes". This premise discharges `NewServer`'s `etcdURLsFit` (fmt stage 1). Carry it |
| `bootPremise` → `bootPremiseDist` | replaced | `bootstrap.wp_proof_dist`. Listed |
| `netHttpOk γn id` → `S5.httpAddrAt peerAddr ∗ □ ∀ pid a, … -∗ S5.httpAddrAt a` | replaced | as `#Hpeers`, plus the member's own address. Listed |
| `memberFreshRes name ⟨some peerAddr, none⟩ γn` → `⌜EtcdVerifyOff⌝ ∗ memberAreasFresh …` | replaced | its file part. The listen right is in `httpAddrAt`. Listed |
| post `memberUp … γn …` → `∃ γn, memberUp …` | post | as above |

## `PeerServe_dist` ↔ `http.Serve_ok` (`Serve_spec`, `Proof/net/http/Boundary.lean:926`)
| difference | kind | justification |
|---|---|---|
| `httpListenerAt l a (H.proto a)` | replaced | → `netListenerOpen pl pa ∗ httpAddrAt γ id pa`, with `γn.N = srvNet γ`. In-process, `register` folds the listener and the address's protocol into `httpListenerAt`. Here the start set the address to etcd's peer protocols of `γ.cl`/`id`. Justified |
| `go!"http://" ++ pa ∈ γn.dir id` | premise added | the member's own address (review of 2026-11-24). Conservative |
| `handlerOk H a Rs h` | replaced | → `peerHandlerOf h s ∗ srvNetMember γn s id τ ∗ isServerReqM on s E ρ`. In-process, `handlerOk` of the raft handler is proved from `srvNetMember`. Here the handler's correctness is the axiom's content (`peerHandlerOf` is opaque, with no laws). Justified |
| `[∗list] … Rs` | instantiated | `Rs := srvServeRes γn τ` (`NewServer_dist`'s post), as in-process. Justified |
| post `True` | same | none |

## `NewPeerHandler_dist`: no in-process counterpart
`etcdhttp` is translated names-only, with no spec. The premises (`zapLoggerOk lg`, `srvNetMember`, `isServerReqM`) are `NewServer_dist`'s and
`Start`'s posts. The post `peerHandlerOf h s` is opaque and read only by `PeerServe_dist`.

## KV client axioms ↔ `Spec/go_etcd_io/etcd/client/v3/kv__*.lean`, `txn__Commit.lean`
All four have R1, R2 (binders `cl V Γ eps`) and R5.

| axiom | counterpart | differences beyond R1, R2, R5 |
|---|---|---|
| `KV_Put_dist` | `kv.Put.spec` | `Γ.auth = false →` added (R2/R3), `dup := false` (R3), `kvErr` dropped (R4). Justified |
| `KV_Delete_dist` | `kv.Delete.spec` | as `KV_Put_dist`. Justified |
| `KV_Get_dist` | `kv.Get.spec` | `dup` gone (the AU is `□` in both, so the spec does not depend on it), `kvErr` dropped (R4). No auth premise: a read is retried only when immutable, as the docstring says. Justified |
| `KV_Compact_dist` | `kv.Compact.spec` | `kvErr` dropped (R4). `1 ≤ rev`, `γ.cmp = true`, `kvRevLbZ` are the same. No auth premise: `NewServer`'s `cmp = true → on = false`. Justified |
| `Txn_Commit_dist` | `txn.Commit.spec` | `Γ.auth = false` (R2/R3), `dup := false` on the outer `□?dup` (R3), `addr := eps` (the builder's endpoints are the client's), `kvErr` dropped (R4). Justified |

## Lease client axioms ↔ `lessor.{Grant,Leases,TimeToLive}.spec` at the server-side `…W` spec
The in-process client specs are generic over a registered `Spec`. Each dist axiom is one of them with its `Spec` fixed (named in its docstring),
`lessorRemoteAtC l conn addr ∗ isGrpcRpcsMd …` replaced by `leaseClientAt cl lp ep V Γ mid` (one endpoint), and these dropped:
`metadata.outMD`, `attemptPre`, `hdrFull`/`ResponseHeader` (auth off, so no metadata; the post is weaker).
All have R1, R4 and `levelTok`.

| axiom | `Spec` | differences |
|---|---|---|
| `Client_LeaseLeases_dist` | `etcdLeaseLeasesSpecAnyW` | post `ids.Nodup`, the same as the spec's. Justified |
| `Client_LeaseTimeToLive_dist` | `etcdLeaseTTLSpecW` | `sl := slice.nil` (`gs = []`). The post keeps the `ID` field only (`m.id = id`), dropping `TTL`, `GrantedTTL`, `Keys`. Justified |
| `Lease_Grant_dist` | `etcdLeaseGrantSpecW (Γ.ls mid)` | `Γ.kv.lm = .mono` (the registration exists in mono mode only). Premise added: distinct `Γ.ls` (F2). Post drops `etcdReached` (no workload reads it). Justified, but sound only with the proposed `Serve_dist` (summary item 3) |
| `Lease_GrantLive_dist` | `etcdLeaseGrantSpecLiveW (Γ.ls mid)` | `Γ.kv.lm = .revocable`, distinct `Γ.ls`. clientv3 sends `ID = 0`, the spec's filter. Same caveat |
| `Lease_LeasesGranted_dist` | `etcdLeaseLeasesSpecW (Γ.ls mid)` | the spec's `∃ G` is made the caller's premise `[∗list] id ∈ G, leaseGrantedAt …`. `.mono`, distinct `Γ.ls`. Same caveat |
| `Lease_LeasesLive_dist` | `etcdLeaseLeasesSpecLiveW (Γ.ls mid)` | the spec's `∃ m, lessorLb` is made the premise `lessorLb (Γ.ls mid) n`. `.revocable`, distinct `Γ.ls`. Same caveat |

## `Client_Put_dist`, `Client_Get_dist` ↔ `client.client_Put_own`, `client_Get_own` (`Proof/go_etcd_io/etcd/client/v3/ClientPutGet.lean`)
These are theorems over `KV_Put_dist`/`KV_Get_dist`, not axioms, so no difference can be unsound. For the record:
- `kvRegsAt ⟨ep,E,γr,cid,mid⟩` → `clientNoProxy cl ∗ etcdAddrAt ep Γ mid`;
- `putGetInv γr …` → `putGetInvK Γ.kv …`;
- dropped: `srvApi.kvLogLb E.γs F`, and for Get `committedAtLeast γr c`;
- Put: `Γ.auth = false` added, and the post's `putReplied …` dropped.
