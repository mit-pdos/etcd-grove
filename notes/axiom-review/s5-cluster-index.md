# Review: the S5 interim peer-transport axioms at the cluster index (`httpPeerSvc γ.cl id`)

The `axiom` skill, run by a fresh agent given the axioms, the vocabulary and the Go code (earlier reviews
read for background only), 2026-11-25. Branch `etcd-safe-n5/2026-11-25`, head `149d218c5d` ("dist: index
the peer protocols by the cluster (httpPeerSvc γ.cl id), not the member's whole SrvRaft"). No Lean built,
nothing committed by the review; Go evidence in a scratch module outside the repository.

**Verdict: all four survive at the new index; docstring changes recommended (exact text below), no
statement change.** Keying the address facts by `(γ.cl, id)` instead of `(γ, id)` does let a reader hold
`httpAddrAt γ' pid a` at a record `γ'` other than the one the member at `a` runs at. No route turns that
into a Go panic or a stuck state:
- every reader that could reach a member's raft is a member of the same cluster, at most once per id. The
  premises of `NewServer_dist` fix every field of its record from `γ.cl` except `reg`, and `srvNet` does
  not read `reg`;
- the only acceptor that can write at a cluster address is that cluster's own member, through
  `PeerServe_dist`. Its `γ` is tied to the server's cluster by `srvNet`'s message predicate at `γ.cl`;
- the one new route (`bootstrap.wp_proof_dist` at a `γ` sharing `γ.cl` but with a stranger's `vs`)
  reaches only etcd's `/members` answer, which never panics `bootstrap` (Go: below).

## What was reviewed

- `etcd_dist.NewServer_dist.wp_proof` (`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/NewServerDist.lean`;
  statement `NewServer.specG_dist` in `Spec/.../examples/etcd/dist/NewServerDist.lean`), its `#Hpeers`.
- `etcd_dist.PeerServe_dist.wp_proof` (`Proof/.../dist/PeerServeDist.lean`, `Spec/.../dist/PeerServeDist.lean`)
  and `etcd_dist.NewPeerHandler_dist.wp_proof` (`.../dist/NewPeerHandlerDist.lean`).
- `bootstrap.wp_proof_dist` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/bootstrapDist.lean`, statement
  `bootstrap.specDist`) through `etcd_dist.bootRTOk`.
- Vocabulary: `S5Interim.lean` (`httpPeerSvc (cl : Cluster) (id : w64)`, opaque, no law;
  `httpAddrAt γ id a := addrProto a (httpPeerSvc γ.cl id).1 (httpPeerSvc γ.cl id).2`; `http_addr_set`;
  `noProxyEnv`; `bootRTOk`; `peerHandlerOf`); `SrvRaft` (`SrvRaftLog.lean:91`); `Cluster` (`InvApi.lean:116`);
  `addrProto`, `addrUnset`, `addr_set_proto`, `listen_au` (`GooseLang/Ext/Net/Proto.lean:381-730`); the
  allocations `srvClusterBoot_allocG`/`srvClusterBoot_alloc` (`NewServerAlloc.lean:203,430`), `clusterAllocN`,
  `memberSlice`, `memberBoot_of_slice`, `memberBoots_of`, `allocN` (`examples/lib/etcdstart/AllocN.lean`).
- Go: etcd fork `e94f33b50` (the examples' pin, `examples/go.mod`), go1.27.3: `etcdserver/cluster_util.go:41-121`,
  `api/etcdhttp/peer.go:108-123`, `api/membership/cluster.go:97-131`, `api/membership/member.go:51-76`.

**What changed.** Before, `httpPeerSvc γ id` over the whole `SrvRaft`. Now `httpPeerSvc γ.cl id`. The text of
the three statements is unchanged. `httpAddrAt γ id a` now depends on `γ` only through `γ.cl`. So
`httpAddrAt γ_A pid a` and `httpAddrAt γ_C pid a` are the same proposition when `γ_A.cl = γ_C.cl`, which is
the point of the change (§19 of `notes/etcd-dist-plan.md`: members' records differ in `reg`,
`memberBoot_of_slice` gives `memberBoot { c.γ with reg := c.reg id }`).

## What fixes a record given its cluster (the facts the routes below use)

A reader at `γ'` with `γ'.cl = cl` must hold `NewServer_dist`'s precondition at `γ'`. Field by field:

| `SrvRaft` field | fixed by (the Lean fact) |
|---|---|
| `cl` | the index |
| `vs` | `Hnboot`'s `nodeBoot γ'.cl srvClusterN γ'.vs ctxs id` = `nodeBootU` (`InvApiBoot.lean:57`): `⌜γ.raft.reCfg = listToSet ps ∧ … ∧ BootLogOk ps γ.raft.reBoot⌝`, and `BootLogOk` (`Protocol/Facts.lean:1643`) gives `ps[k]` = the node id of `reBoot[k]`, a pure field of `cl` |
| contexts `ctxs` (Go-visible) | `nodeBootU`'s `bootMarshal ps ctxs γ.raft.reBoot` (the boot entries' bytes are `cl`'s) |
| `boot` | `srvRaftLogInv`'s `srvRLogLb γ (γ.raft.boot.map ofM)` = `isCommittedLogLb γ.raft.cl …` and `srvClusterOk`'s `⌜γ.raft.cl.bootLen = γ.raft.boot.length⌝` (`SrvRaftLog.lean:946-1018`): a prefix of `cl`'s committed log of a fixed length |
| `rule` | the premise `γ.rule = srvRule (W64 0) γ.boot` |
| `snapLoc` | `srvClusterOk`'s `⌜γ.raft.cl.snapLoc = γ.raft.snapLoc⌝` |
| `log`, `props`, `fired`, `pend`, `fresh` | `srvLogInv` (`SrvRaftLog.lean:854`) keeps `srvLogCore`'s `ownCommittedOps γ.raft.cl …`, the client's half of `cl.ops` (`InvApi.lean:344`, exclusive, given once by the cluster's allocation): one `srvLogInv` per cluster |
| `rdFresh` | `srvRdCtxInv`, allocated from `srvLogInv_alloc`'s exclusive `Hrdf` and `cl`'s read contexts |
| `authOn` | `kvInvM on` gives `⌜γ.raft.authOn = on⌝` (`kvInv_authOn`, `KVAuthModel.lean:2028`; `kvInvOn`'s at `true`). Its allocation (`kvInv_alloc_boot`, `kvInvOn_alloc`) takes `srvRLog γ []`, the half of `γ.log`'s authority outside `srvLogInv` (`SrvRaftLog.lean:389`): one KV invariant, so one auth mode, per cluster |
| `reg` | free: the member's own `MemoryStorage` registry (`memStorRegAuth ∅` at `⟨γ.reg⟩`), a ghost name of one process, not Go-visible. `srvNet` does not read it: `leaseN`'s `Main` closes `γn.N = srvNet { γ with reg := r }` from `γn.N = srvNet γ` by `refine` (definitional) |

So the records of two members of one cluster differ at most in `reg`. They are the records of one in-process
network (`allocN`: `γn.N = srvNet γ`, each member at `{ γ with reg := r }`). This mapping is what
`NewServer_dist`'s "why it is true" relies on (`NewServer.wp_proofG` over the in-process network). Each
member's Go configuration (ids, contexts, boot entries, auth mode) is the cluster's.

`srvNet γ` (`InvApplyAll.lean:102-111`) reads `γ.cl` (`P := ∃ sid, sentMsg γ.cl srvClusterN sid st`,
`O := msgCredits γ.cl …`, `Sz := γ.cl.maxData ≠ none`) and `γ.authOn` with `srvImageM γ.authOn γ`. Two
allocations of a cluster have fresh ghost names, so their message predicates differ in the model. No proof
derives `srvNet γ = srvNet γ₂` across two allocations: it would be a false pure fact from satisfiable
resources.

## Verdict per axiom

- **`NewServer_dist`: survives.** Every peer it dials is at an address set once to `(γ.cl, pid)`. The only
  acceptor writing there is member `pid` of `γ.cl` (`PeerServe_dist`). The other members dialing there are
  members of `γ.cl`, one per id. Recommended: docstring D1, D2.
- **`PeerServe_dist`: survives.** Its free `γ` is tied to the server's cluster through `srvNet`. The
  dialers at `pa` are members of `γ.cl` (through `NewServer_dist`) or hold `httpAddrAt` and write nothing.
  The known `leasehttp.RenewHTTP` route is index-independent (route B review, `notes/etcd-dist-plan.md`
  §17.3). Recommended: docstring D3.
- **`NewPeerHandler_dist`: survives.** It mentions no address. The change does not touch it.
- **`bootstrap.wp_proof_dist`: survives.** It has one new route (R6): a caller at a `γ` sharing `γ.cl` with
  its own configuration's `vs`. It is harmless: the answer is still etcd's peer handler's. Recommended:
  docstrings D4, D5.

## Routes examined

**R1. A second ghost cluster with the same configuration at the first's addresses (the 2026-11-24
counterexample's shape).** Blocked. A second `srvClusterBoot_alloc` returns another `cl₂` (fresh names). Its
member's `Hpeers` needs `addrProto a (httpPeerSvc cl₂ pid)` at an address set to `httpPeerSvc cl pid`.
`addrProto a P Q` is an invariant holding `a`'s exclusive pending set (`addrUnset`'s `netPend NG a ∅`,
spent by `addr_set_proto`, `Proto.lean:724`), so `a` has one protocol pair. `httpPeerSvc` is opaque with
no law, so no proof equates its values at `cl` and `cl₂`. The other direction needs `PeerServe_dist` for
`cl₂`'s member at `a`, with `httpAddrAt γ pid a` at `γ.cl = cl` and `srvNet γ = srvNet γ₂` (`γ₂.cl = cl₂`).
That needs `sentMsg cl = sentMsg cl₂`, which is false of two allocations (above).

**R2. A duplicate of a member inside `γ.cl` (two processes for one `(cl, id)`).** Blocked, as before:
`raftState γ.cl id RaftState.init ∗ nodeVacant γ.cl id` in `Hnboot` are exclusive and given once per id
(`srvClusterBoot_allocG`'s per-member conjuncts; `memberSlice`). `nodeBoot` is persistent and does not
block it. The block is per ghost name. A "phantom" `cl'` equal to `cl` in names but different in a pure
field nobody reads shares those exclusive resources, so it adds no member. Its addresses are served only
by `cl`'s members (R3).

**R3. A record `γ'` with `γ'.cl = γ.cl` but other fields different (`vs`, `rule`, `boot`, `snapLoc`,
`authOn`, the log names, `reg`), as a reader under `NewServer_dist`.** Blocked for every field but `reg`
(the table): the reader cannot meet its precondition at such a `γ'`. `reg` differs by design and is not
read by `srvNet`. Under the old index the same pinning held, but the readers' `reg`s had to be equal
too, which no start could give at three members.

**R4. Two members at one cluster's address.** Blocked. Member `pid₂ ≠ pid` serving at `a` (set to
`(cl, pid)`) needs `httpAddrAt γ pid₂ a` for `PeerServe_dist` (its `srvNetMember γn s id` fixes the id):
another protocol pair at `a`, unobtainable (R1's pending-set argument; `httpPeerSvc cl pid` and
`httpPeerSvc cl pid₂` are not provably equal). A reader whose directory names one address for two ids needs
both facts at it, equally unobtainable (and `netDirOk` keeps the hosts apart).

**R5. A member and a stranger at one cluster's address.** No panic. Anyone the start gives `httpAddrAt`
may listen (`listen_au`, with the exclusive `netAddrRsv` that `net.Listen.spec` takes), dial and accept
at `a`. Go answers a second listener with `EADDRINUSE`, an error. The opaque protocols let no proof write
bytes there, so a stranger listener is a peer that never answers, which the transport handles (timeouts).
Index-independent.

**R6. `bootstrap.wp_proof_dist` at a record sharing `γ.cl` with another configuration (new with this
index).** Its `γ` is constrained only by pure premises tying `γ.vs` and `γ.boot` to its own configuration
(`γ.vs = bootGo.ps U token`). `bootRTOk γ id dir` reads `γ.cl` and `γ.vs`. So a caller with
`γ := { real with vs := its ids, boot := … }` meets `bootRTOk` wherever its directory names a real member's
address under the real member's id. This holds when its entry for that member has the same URL and token:
`computeMemberID` hashes the sorted peer URLs and the token, `member.go:63-76`. Under the old index
`γ.vs` had to be the real record's. The GET then reaches the real member's peer handler, whose `/members`
is `json.Encode(cluster.Members())` (`peer.go:108-123`). `Members()` returns `m.Clone()` of each member,
non-nil (`cluster.go:123-131`). `NewClusterFromMembers` (`cluster.go:97-104`) and `rcl.Member(id)` cannot
panic on that. The answer makes `isMemberBootstrapped` answer `false` (the boot goes on) or `true` (the
error "has already been bootstrapped"). The axiom's one panic route, a `null` element, still needs a
non-etcd writer at `a` or a proxy (`bootstrap-dist.md` A1, A2), which `bootRTOk` still excludes. Go
evidence: below. The route does not reach a run of the transport. `bootstrap` is unexported, so only
`NewServer` calls it. `NewServer_dist`, and the in-process `NewServer.specG`, take
`Hnboot` at `γ.cl, γ.vs`, whose `nodeBootU` pins `vs` to `cl`, so a stranger configuration's raft never
starts at `cl`'s addresses. The in-process route to those addresses is closed by `http.reserve` taking the
pending set (`http-reserve-pend.md`).

**R7. `PeerServe_dist`'s `γ`, constrained only by `γn.N = srvNet γ` and `pa ∈ γn.dir id`.** Blocked. A
`γ` whose `γ.cl` is another allocation's fails the `srvNet` equation (R1). A `γ` over the server's own
cluster with other fields is harmless: `httpAddrAt` reads only `γ.cl`, and the server, the listener, the
handler and the per-request resources are fixed by `srvNetMember γn s id τ`, `isServerReqM`,
`peerHandlerOf h s` and `netListenerOpen pl pa`. `pa` is the server's own directory entry. A second
address set to `(cl, id)` is served by member `id` only if it is in its own directory. Otherwise it is
silent (R5).

**R8. Readers with different directories for one member.** Index-independent (the whole-`γ` index allowed
it too). Member A naming `b₁` for B and member C naming `b₂` needs both set to `(cl, B)` (two `addrUnset`s).
Only B's peer handler writes at either, and only at an address in B's own directory. Moreover the
directories come from the boot contexts (`bootURLsOk γ.raft.boot`, `bootGo.dir`), which `cl` fixes.

**R9. Persistent facts used across worlds (the `crossWorld` check).** Not applicable. No law derives a pure
fact from `httpAddrAt`, `bootRTOk` or `noProxyEnv`. `httpPeerSvc` has no law, and `addrProto`'s agreement
is an internal equivalence of protocols, not a pure equation of an opaque function of a pointer.

Not tried (as in the earlier reviews): the crash law and the restart path (a restarted member's
`raftState`/`nodeVacant`); the names-only `leasehttp.RenewHTTP` route beyond what route B's review did.

## Go evidence

Scratch module `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/n5-scratch/review/stranger/` (not in the repository;
`examples/go.mod`'s pins, go1.27.3, `TMPDIR` in the scratch directory). `TestStrangers` brings up a real
three-member cluster: `NewServer`, `etcdhttp.NewPeerHandler` served on each peer address, `Start`, all
`ReadyNotify`, published with client URLs. Then strangers run `NewServer`, whose `bootstrap` sends
`GET /members` to the real members. 3/3 runs, no panic:

```
real cluster up: a=c31bb598ec0a5123 b=2ceba1a3935f3355 c=546f6b57f573e2e5
s1 (token real): NewServer returned a server, id 1eb6d57e5c96eb9c (not started)    # {a's URL, s1}
b (token real): NewServer returned an error: member 2ceba1a3935f3355 has already been bootstrapped   # clone of b
s3 (token other): NewServer returned a server, id b575fd5047c108f5 (not started)   # {a's URL, s3}, other token
s4 (token real): NewServer returned a server, id 4baaed6cc3199421 (not started)    # {b's URL as "x", s4}
--- PASS: TestStrangers (1.35s)
```

Together with `examples/axiomcx/bootstrapdist` (`TestBootThreeMembers`: members of the cluster answered by
a member's handler; `TestNullMemberAtPeer`, `TestProxyNull`: the two excluded panics), this shows the
claim R6 needs: at the pin, no answer of etcd's peer handler, of any cluster, panics `bootstrap`.

## Recommended docstring changes (exact text; no statement change)

**D1. `NewServer_dist.wp_proof`** (`Proof/.../dist/NewServerDist.lean`). After "...the transport's own code
being the same." insert:

> Across machines the members of one cluster read the address facts at their own records, which
> agree on `γ.cl` (the index of `httpAddrAt`) and differ at most in the storage registry `γ.reg`: given
> `γ.cl`, this precondition fixes the rest (`vs` by `nodeBoot`'s `BootLogOk vs γ.cl.raft.reBoot`, `boot` by
> `srvRaftLogInv`'s committed lower bound of length `γ.cl.bootLen`, `rule` by the premise, `snapLoc` by
> `srvClusterOk`, the log names by `srvLogInv`'s `ownCommittedOps γ.cl`, `authOn` by `kvInvM on`, one per
> cluster), and `srvNet` does not read `reg`: the members are those of one in-process network
> (`allocN`'s `γn.N = srvNet γ`), with the cluster's ids, contexts and auth mode.

**D2. `NewServer.specG_dist`'s file header** (`Spec/.../dist/NewServerDist.lean`). Replace "the deployment's
start set `a` to etcd's peer protocols of the cluster `γ` and member `pid`" with "the deployment's start set
`a` to etcd's peer protocols of `γ`'s cluster `γ.cl` and member `pid`; `httpAddrAt` reads `γ` only through
`γ.cl`".

**D3. `PeerServe_dist.spec`** (`Spec/.../dist/PeerServeDist.lean`). Replace "`pa` set to etcd's peer
protocols of `s`'s cluster and member (`httpAddrAt γ id pa`)" with "`pa` set to etcd's peer protocols of
`s`'s cluster and member (`httpAddrAt γ id pa`, at a `γ` whose network payload is `s`'s, `γn.N = srvNet γ`:
`srvNet`'s message predicate is at `γ.cl`, so `γ.cl` is `s`'s cluster)".

**D4. `bootRTOk`** (`S5Interim.lean`). Replace "has its address `a` set to etcd's peer protocols of `γ` and
`pid` (`httpAddrAt`)" with "has its address `a` set to etcd's peer protocols of `γ`'s cluster `γ.cl` and
`pid` (`httpAddrAt`; `γ`'s other fields, here only `γ.vs`, are the caller's)".

**D5. `bootstrap.wp_proof_dist`** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/bootstrapDist.lean`). Replace
"the answer is from etcd's peer handler of a member of the same cluster (`httpPeerSvc`'s acceptor protocol),
whose `/members` is a JSON list of members." with:

> the answer is from etcd's peer handler of member `pid` of the cluster `γ.cl` (`httpPeerSvc`'s acceptor
> protocol, written only by `PeerServe_dist`), whose `/members` is a JSON list of members. The axiom ties `γ`
> to this configuration only by pure premises (`γ.vs` its ids), so that member may have been started from
> another configuration; the axiom needs only that the answer is etcd's: any etcd member's `/members` is
> `cluster.Members()`'s `Clone`s, never `null` (`membership/cluster.go:123-131`; scratch evidence in
> `notes/axiom-review/s5-cluster-index.md`: strangers answered by a real three-member cluster boot or get
> "has already been bootstrapped", no panic).

**D6. `httpPeerSvc`** (`S5Interim.lean`), optional precision. Replace "an address is set once (`addrUnset` is
spent), so only one cluster's members, and only the member `id`, are at it." with "an address is set once
(`addrUnset` is spent), so the only acceptor writing at it is member `id` of `cl` (`PeerServe_dist`, whose `γ`
`srvNet` ties to the server's cluster) and the only dialers writing there are members of `cl`
(`NewServer_dist`, one per id: `raftState`/`nodeVacant`); a second allocation of the same configuration is
another `cl`."

The skill's bookkeeping (an index row in `notes/axiom-review/README.md`; these axioms have no
`notes/audit.md` row yet, §17.3's last paragraph) is left to the branch owner: this review changed only this
file.
