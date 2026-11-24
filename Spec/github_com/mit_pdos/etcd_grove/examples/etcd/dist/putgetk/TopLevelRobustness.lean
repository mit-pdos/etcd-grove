/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: `putgetK_safe` at `k = 3`, stated (DRAFT for review)

**Three etcd members, each on a machine of its own, and one client on another** (`notes/putget-dist-plan.md`
§13: `putget_safe`, `Spec/.../examples/etcd/dist/putget/TopLevelRobustness.lean`, with a cluster of `k`
members; no machine crashes). Member `i`'s machine (`i < 3`) runs `putgetk.Member(i, peers, clients)`
(`examples/etcd/dist/putgetk`: member `i` of a new three-member cluster, built as the in-process
`putgetN` builds each member, its raft handler served on its peer address, etcd's gRPC API at its client
address, the process kept alive); the client machine runs `putgetk.Client(endpoint)` (putget's client
against member `0`'s client address: a `Put` of `k` with `v`, a `Get` of `k`, a panic unless the `Get`
returned `v`; an error from any step ends it without the check). **In every execution** of Perennial's
distributed semantics over the net extension (any interleaving of the four machines' threads; every fault
the net extension allows: bytes delayed, a direction cut at any read or write, a dial refused; a
partition, of the members from each other or of the client, is such an execution) of fewer than `bound`
steps along which each machine keeps fewer than `threads` threads, **no thread of any machine is stuck or
has an unrecovered panic** (`Robust`). The client panics if the `Get` after an acknowledged `Put` returns
another value, so it never does: the cluster's raft replication across the members' machines keeps the
acknowledged `Put`.

**The deployment is fixed** (`TopLevelDefs.lean`): member `i` named `putgetk-i` on the machine
`10.77.(i+1).1`, its peer address on port `2380`, its client address on port `2379` (the namespace test
`TestPutGetK`'s); the cluster's token `putgetk`. The statement for any `k` (the members and addresses a
parameter, `addrOk` and distinct) comes after this one is reviewed.

**The premises**, per member where putget's are per machine:
- the deployment: the six addresses distinct and valid, no connection, no listener (`DistDeploy`); each
  machine's files as on disk (`FsInit`, in `MemberFiles` and `ClientFiles`), and member `i`'s data
  directory and WAL area empty on its machine (`MemberFiles i`);
- `bootstrap`'s results for the cluster (`BootFacts ids ps ctxs boot`, the in-process `putgetN`'s): the
  member ids `ids` in the members' order (etcd's, from each peer URL and the token; `TestMemberIDs` checks
  their 16 low bits distinct and not `0` at these addresses), the peers `ps` (a permutation of the ids),
  their contexts and the bootstrap log;
- carried over from `putget_safe` until discharged: the server's workload and environment premises
  (`authRecordsFit`, ...), the members' named Iris premises (`Hprem`: per member `bootstrap`'s contract
  at its configuration and URLs, at the cluster's peer-URL directory, `proto.Marshal`'s at the bootstrap
  log, the raft wrapper's contracts: `premises`, the in-process `putgetN`'s form; at every ghost-state
  instance), `context`'s two classes (`Hctx`, `Hcec`);
- `ETCD_VERIFY` off on every machine's run (`HEnv`) and its token (`HEnvTok`), as `putget_safe`'s.

**The step bound** is `putget_safe`'s, `2 ^ 28 - 1` (until perennial#690). **What the semantics assumes**
(not premises): `putget_safe`'s (the file extension at `etcdFsSem` on every member's machine; the request
ids' issue record keyed by heap address, sound with no crash).

**Trusted gap**: the binaries (`cmd/{member,client}`) parse their arguments; the parsing is not translated,
so member `i`'s boot program is `Member` applied to `i` and the two address lists as Go slice literals
(`strSliceLit`), the client's `Client` applied to member `0`'s client address (its result discarded).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.TopLevelDefs
public import Proof.runtime.Start
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Init
public import Proof.log.NewModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Robustness go_etcd_io.raft.v3 etcd_putget_dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- **`putgetK_safe` at `k = 3`** (see the file header): the deployment of three member machines and one
client machine, none of which crashes, is robust: no thread of any machine is stuck or has an unrecovered
panic, so the client's `Get` after an acknowledged `Put` returns the `Put`'s value. -/
def putgetK_safe.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    -- bootstrap's results for the cluster's configuration (the member ids in the members' order, the
    -- peers in bootstrap's order, their contexts, the bootstrap log)
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hids : ids.length = 3)
    (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    -- the server's workload and environment (putget_safe's)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the members' named premises, at every ghost-state instance (putgetN's form of putget_safe's)
    (Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) n ids ps ctxs boot)
    -- the machines' start states: member i's from σs[i], the client's from σc
    (σs : List state) (σc : state) (g : GlobalState) (Hσs : σs.length = 3)
    (Hm : ∀ (i : Nat) (σ : state), σs[i]? = some σ → MemberFiles i σ) (Hc : ClientFiles σc)
    (Hd : Net.DistDeploy addrs (system σs σc) g)
    -- `ETCD_VERIFY` off on every machine's run, and its token in the logic (putget_safe's)
    (HEnv : ∀ m ∈ system σs σc, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := putgetGF)),
    Robust [] (system σs σc) g (threads := 2 ^ 28) (bound := 2 ^ 28 - 1)

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
