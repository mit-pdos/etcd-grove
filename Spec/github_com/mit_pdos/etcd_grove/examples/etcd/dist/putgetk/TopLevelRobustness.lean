/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: `putgetK_safe`, stated for any configuration of members (`notes/putget-dist-plan.md` §13)

**An etcd cluster of any number of members, each on a machine of its own, and one client on another.**
`putget_safe` (`Spec/.../examples/etcd/dist/putget/TopLevelRobustness.lean`) with a cluster of `n` members,
no machine crashing. The configuration is the statement's parameter, any two lists `peers` and `clients`
of addresses: member `i`'s machine (one per peer address) runs `putgetk.Member(i, peers, clients)`
(`examples/etcd/dist/putgetk`), the client machine `putgetk.Client(clients[0])`. `Member` first checks what
etcd needs of the configuration (`putgetk.Valid`: a member, one client address per peer address, every
address valid and the `2n` addresses distinct, the member ids' 16 low bits distinct and not `0`; the ids
computed as etcd computes them, `putgetk.MemberID`) and returns if it does not hold; else it is member `i`
of a new `n`-member cluster (built as the in-process `putgetN` builds each member), its raft handler served
on its peer address, etcd's gRPC API at its client address, the process kept alive. `Client` (if its
endpoint is valid) is putget's: a `Put` of `k` with `v`, a `Get` of `k`, a panic unless the `Get` returned
`v`; an error from any step ends it without the check. **In every execution** of Perennial's distributed
semantics over the net extension (any interleaving of the machines' threads; every fault the net extension
allows: bytes delayed, a direction cut at any read or write, a dial refused; a partition is such an
execution) of fewer than `bound` steps along which each machine keeps fewer than `threads` threads, **no
thread of any machine is stuck or has an unrecovered panic** (`Robust`). The client panics if the `Get`
after an acknowledged `Put` returns another value, so it never does.

**Not vacuous**: `TestNonVacuity` (`examples/etcd/dist/putgetk`) runs the deployment over seeded random
configurations of 1 to 5 members, which `Valid` accepts, and the client's check runs in each;
`TestValidSeeds`: `Valid` accepts 19998 of 20000 random configurations of 1 to 9 members (the two others:
colliding id prefixes); `TestMemberIDEtcd`: `MemberID` is etcd's id on 3000.

**The premises** (`putget_safe`'s, at `n` members; none on the configuration's values but `DistDeploy`'s):
- the deployment: the `2n` addresses distinct and valid, no connection, no listener (`DistDeploy`,
  `putget_safe`'s and the bridge's: below); each machine's files as on disk (`FsInit`, in `MemberFiles` and
  `ClientFiles`), and member `i`'s data directory and WAL area empty on its machine (`MemberFiles i`);
- `bootstrap`'s log (`BootLogFacts (idsOf peers) ps ctxs boot`: the peers `ps` a permutation of the ids,
  one conf change per peer, ...): what `bootstrap` produces, at the ids etcd computes (`idsOf`); the ids'
  own conditions are the program's check, not a premise;
- carried over from `putget_safe` until converted to axioms in their functions' files (the survey of
  2026-11-24): the server's workload and environment premises (`authRecordsFit`, ...), the members' named
  Iris premises (`Hprem`: per member `bootstrap`'s contract at its configuration and URLs, at the
  cluster's peer-URL directory and at the ids etcd computes, `proto.Marshal`'s at the bootstrap log, the
  raft wrapper's contracts: `premises`, the in-process `putgetN`'s audited form; at every ghost-state
  instance), `context`'s two classes (`Hctx`, `Hcec`);
- `ETCD_VERIFY` off on every machine's run (`HEnv`) and its token (`HEnvTok`), as `putget_safe`'s;
- **new**: the `fips140` GODEBUG setting unset or `off` (`Hfips`, Perennial's environment premise
  `crypto.fips140.GodebugFips140Off`): the members' check computes the ids with `crypto/sha1`, whose `Sum`
  panics under `fips140=only`.

**The step bound** is `putget_safe`'s, `2 ^ 28 - 1` (until perennial#690). **What the semantics assumes**
(not premises): `putget_safe`'s.

**Trusted gap**: the binaries (`cmd/{member,client}`) parse their arguments; the parsing is not translated,
so member `i`'s boot program is `Member` applied to `i` and the two address lists as Go slice literals
(`strSliceLit`), the client's `Client` applied to member `0`'s client address (its result discarded).

**`DistDeploy`'s addresses** stay a premise (as `putget_safe`'s): the bridge `robust_of_distBootIL` takes
them. With the program's check, a variant without them (the start claiming no address when the
configuration is invalid) is a follow-up.
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

/-- **`putgetK_safe`** (see the file header): the deployment of one member machine per peer address and
one client machine, none of which crashes, is robust for every configuration: no thread of any machine is
stuck or has an unrecovered panic, so the client's `Get` after an acknowledged `Put` returns the `Put`'s
value. -/
def putgetK_safe.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    -- the configuration: any members' peer and client addresses
    (peers clients : List GoString)
    -- bootstrap's log at the ids etcd computes (the peers in bootstrap's order, their contexts, the log)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbl : BootLogFacts (idsOf peers) ps ctxs boot)
    -- the server's workload and environment (putget_safe's)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the members' named premises, at every ghost-state instance (putgetN's form of putget_safe's)
    (Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) n peers clients ps ctxs boot)
    -- the machines' start states: member i's from σs i, the client's from σc
    (σs : Nat → state) (σc : state) (g : GlobalState)
    (Hm : ∀ i < peers.length, MemberFiles i (σs i)) (Hc : ClientFiles σc)
    (Hd : Net.DistDeploy (addrs peers clients) (system peers clients σs σc) g)
    -- `ETCD_VERIFY` off on every machine's run, and its token in the logic (putget_safe's)
    (HEnv : ∀ m ∈ system peers clients σs σc, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := putgetGF))
    -- the `fips140` GODEBUG setting unset or `off` (`crypto/sha1`, the members' check)
    (Hfips : crypto.fips140.GodebugFips140Off),
    Robust [] (system peers clients σs σc) g (threads := 2 ^ 28) (bound := 2 ^ 28 - 1)

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
