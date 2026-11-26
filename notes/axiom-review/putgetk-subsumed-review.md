# Does `etcd_safe_nocrash` (B) subsume `putgetK_safe` (A)? Independent review

Reviewed at `origin/etcd-safe-nc-n2/2026-11-25` (`b35f8f67ca`), from the Go programs and the two statement
files only (no Lean build).

- A: `examples/etcd/dist/putgetk` (`Member`, `Client` = `putget.Client`), statement
  `putgetK_safe.spec` (`Spec/.../examples/etcd/dist/putgetk/TopLevelRobustness.lean`).
- B: `examples/etcd/dist/{server,client,deployment,kvremote}`, statement `etcd_robust_nocrash.spec`
  (`Spec/.../examples/etcd/dist/TopLevelRobustness.lean`).

**Verdict: B does not strictly subsume A.** A's one client check is the same predicate as B's putget
workload's check, and every configuration A accepts maps to a deployment B's `WellFormed` accepts. But B's
member program is a different program from A's, and three of the differences remove executions in which A's
check runs. The largest: A's member serves gRPC before it is ready, and B's never does. B also has one
premise that A lacks (`leasePeersOk`). In the other direction, A has two premises that B lacks (B is
stronger there).

## 1. A's checks and what in B covers them

A's Go code has exactly one explicit panic. Its other panics are etcd's internal assertions, which run inside
the member program.

| A check | Property, A's scope | B check covering it | Status |
|---|---|---|---|
| `examples/etcd/dist/putget/putget.go:140-141` (reached from `putgetk/putgetk.go:176`) | The `Get` after an acknowledged `Put` returns the `Put`'s value (`len(Kvs)==0 \|\| Value != v` → panic). Scope: k = 1..64 members, one client machine with one client of the endpoint `[clients[0]]`, one `Put("k","v")` and then one `Get("k")`, the first error ends the run without a check. | `examples/etcd/dist/client/compact.go:148-149` (`RunPutGet`, round 0), reached through `client.go:152-153` ← `MainDeployment` `client.go:173` ← `Orchestrator` `client.go:186`. Deployment: `Members[j] = {putgetk-j, peers[j], clients[j]}`, `Token "putgetk"`, `Cfg{Retention 0, SnapCount 10000 (NoSnapCount), CatchUp 1<<48, Auth false}`, `Workloads [{PutGet}]`, `Nodes [[]]`. | **Covered, with gaps.** The predicate is the same. The key and value are renamed (`pg/k0`/`v0` for `k`/`v`, with no other writer in the store). B runs 50 rounds, and its round 0 runs under the same conditions as A's single round. Gaps: (G1) A's member serves gRPC before `ReadyNotify` and B's does not. (G2) at k > 1, B's client has every endpoint, not member 0's alone. (G3) B's member returns when an HTTP proxy variable is set. |
| etcd's internal assertions in A's member (raft, etcdserver, mvcc and wal panics), via `putgetk.go:157-162` → `etcdstart.StartMember`/`Serve` (`lib/etcdstart/common.go:180-221`) | etcd's own invariants. Scope: A's fixed server configuration, `RaftHandler` alone on the peer listener (opened before `Start`), gRPC served right after `Start`. | `server/server.go:182-213`: the same `etcdserver.NewServer`, `Start` and `v3rpc.Server`, with field-for-field equal configuration values for A's deployment. The compactor mode is `""` where A's is `"revision"`, but etcd reads the mode only when the retention is not 0 (`etcdserver/server.go:380`). | **Partially covered.** Same etcd code and same configuration, but a different member program. (G1) the gRPC timing. (G4) B serves the full `etcdhttp.NewPeerHandler`, so a peer's `/members`, `/leases` and `/version` requests get answers, where A's get 404. B also opens its peer listener only after `Start`. (G3) the proxy variables. |

`putgetk.Valid`, `AddrOK` and `Member`'s early return are not checks: they return, they never panic. The
SHA-1 inside `MemberID` could panic, but both statements exclude that with `Hfips`.

## 2. Scope, dimension by dimension

| Dimension | A | B | B ⊇ A? |
|---|---|---|---|
| Members | 1..64 (`Valid`: at least 1; the premise `Hbgo`/`bootGoAt`: at most 64) | 1..64 (`WellFormed` clause 1) | equal |
| Names | fixed `putgetk-j` | any `nameOk`, distinct, at most 255 bytes | yes |
| Token | fixed `putgetk` | any nonempty string of at most 255 bytes | yes |
| Addresses | `AddrOK`, all 2k distinct | `AddrOk`, all 2k plus the client machines' distinct | equal for putget, which has no client machines. `AddrOK` and `AddrOk` agreed on 200k random strings. |
| Member ids | 16 low bits distinct and not 0 (`sha1("http://"+peer+token)`) | the same (`membership.NewMember`), plus 15 low bits distinct only if a workload grants leases | equal for putget |
| Embedding | — | a scratch test (deleted afterwards) on 20000 random configurations of 1..70 members: `Valid ∧ k≤64` ⇔ `WellFormed(embed) == nil` held in every case, 7536 of them valid | yes |
| Server configuration | fixed: snapshot count 10000, catch-up 2^48, compactor off, no auth | snapshot count ≥ 1, catch-up ≥ 1, compactor off, revision ≥ 1 or periodic ≥ 10, auth on or off | yes |
| Client machines | 1 | one orchestrator per workload, plus client machines (putget alone: 1) | yes |
| Client endpoints | `[clients[0]]` | `d.Endpoints()`, all k | equal at k = 1. At k > 1 B covers A's executions only through a choice of B's client: round_robin with the dials to the other endpoints refused (the network may refuse any dial). This depends on the grpc client model allowing it (**G2**). |
| Operations | 1 `Put` and 1 `Get`, key `k`, ends at the first error | 50 rounds of `Put` and `Get` on `pg/k_i`, a round skipped on error | yes, up to the key renaming |
| Check predicate | `len(Kvs)==0 \|\| Value != v` | the same | equal |
| Steps | fewer than 2^28 − 1 | fewer than 2^48 | yes |
| Threads | fewer than 2^28 | fewer than 2^28 | equal |
| Crashes and network faults | none; the net extension's | none; the same | equal |
| Member timing | peer listener before `Start`, gRPC served right after `Start` | peer listener after `Start`, gRPC only after `<-ReadyNotify()` (`server.go:187-213`) | **no (G1)** |
| Environment | any value of `HTTP(S)_PROXY` | the member returns if one is set (`server.go:175`), so B's check runs only with none set | **no (G3)** |
| Peer HTTP surface | `RaftHandler` only | the full peer handler | **different (G4)** |

## 3. Premises

| Premise | A | B | Comparison |
|---|---|---|---|
| Boot log | `BootLogFacts (idsOf peers)` | `BootFacts d` = `BootCore` + `perm` | `BootCore` adds `lowNodup`/`lowNz`, which follow from `perm` plus the ids check on every configuration where a check runs. Equal there. |
| What `bootstrap` computes | `Hbgo : BootGoK` (at most 64 members, `bootGo.*`) | — | **A only**: A excludes more, so B is stronger here |
| Addresses distinct and valid | `Hd : DistDeploy` (also no connection, no listener) | — (checked by the program; the network's start is `Robust`'s own) | **A only**: B is stronger here |
| `authRecordsFit`, `backendUnderQuota`, `grpcRepliesFit`, `diskOk` | yes | yes (in `EtcdEnv`) | the same opaque propositions |
| `leasePeersOk` | — | `EtcdEnv.leasePeers` | **B only.** An opaque Prop, so formally B's result is conditional on it and A's is not. Its intended meaning holds for both deployments (A's peers answer 404, B's answer as etcd's handler). |
| `leasesNoExpiry` | — | only if a workload needs it | does not apply to putget |
| `peerRequests` | — | `True` (a placeholder) | none |
| Start files | `MemberFiles i`, `ClientFiles` | `ServerStart`, `ClientStart` | equal at the names `putgetk-j` |
| `EtcdVerifyOff`, `GodebugFips140Off` | yes | yes | equal |
| Instance binders | `putgetk.Assumptions`, cache, `DialWithBalancerBody`, `log.NewModel`, `net.FieldAssumptions` | server and client `Assumptions`, `errors`, `fmt`, `rpctypes`, cache, `DialWithBalancerBody`, `log.NewModel`, `net.FieldAssumptions` | These are the translations' own classes (function unfolding) for the programs they name. They do not exclude runs. |

## 4. Verdict and gaps

**B does not subsume A.** A's check (one `Put`/`Get` pair, the same predicate) appears in B's putget
workload at a deployment B covers whose scope is at least as wide in members, names, token, addresses, ids,
server configuration, operations, steps and threads. The gaps:

- **G1 (the substantive one).** A's member serves etcd's gRPC API right after `Start`, before
  `ReadyNotify`. B's member serves it only after `ReadyNotify`. An execution in which A's `Put` or `Get`
  is served by a member that is not ready yet is not an execution of B's programs, so a bug that makes a
  read before readiness stale (the class behind review F4) is excluded by A and not by B.
- **G2.** At k > 1, A's client uses member 0 alone and B's uses every member. B covers A's executions only if
  B's client can send all of its calls to member 0 (round_robin with the other dials refused). That is
  plausible, but it rests on the grpc client model rather than on the programs being the same.
- **G3.** B's members return when `HTTP_PROXY`, `http_proxy`, `HTTPS_PROXY` or `https_proxy` is nonempty.
  A's members have no such check, so A covers runs in those environments; for example at k = 1, where no
  peer traffic exists, A's check runs and B's statement holds only because nothing runs.
- **G4.** The member programs differ in their peer handler (`RaftHandler` alone vs etcd's full peer
  handler) and in when the peer listener opens relative to `Start`. etcd's internal assertions reachable only
  under A's peer surface or ordering are not exercised by B.
- **Premise.** `leasePeersOk` is B's only extra premise: an opaque Prop, benign in its intended meaning, but
  formally B's result is conditional on it.
- **Negligible.** The key and value literals differ (`pg/k0`/`v0` vs `k`/`v`).

Closing G1 to G4 needs either B's member to cover A's construction or B to keep A as a separate result.
Simply retiring A would drop the executions in G1 and G3.
