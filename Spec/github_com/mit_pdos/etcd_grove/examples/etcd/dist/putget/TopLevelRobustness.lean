/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: `putget_safe`, etcd's first distributed theorem, stated

**One etcd member on a machine of its own and one client on another** (`notes/putget-dist-plan.md`; the
interim form of `etcd_safe`, `notes/etcd-dist-plan.md` Q7: no machine crashes). The member machine runs
`putget.Member(peer, client)` (`examples/etcd/dist/putget`: the one member of a new cluster, etcd's gRPC
API served at `client`, the process kept alive), the client machine `putget.Client(client)` (a client of
the member's client address, a `Put` of `k` with `v`, a `Get` of `k`, a panic unless the `Get` returned
`v`; an error from any step ends it without the check). **In every execution** of Perennial's distributed
semantics over the net extension (any interleaving of the two machines' threads; every fault the net
extension allows: bytes delayed, a direction cut at any read or write, a dial refused; a partition is
such an execution) of fewer than `bound` steps along which each machine keeps fewer than `threads`
threads, **no thread of either machine is stuck or has an unrecovered panic** (`Robust`). The client
panics if the `Get` after an acknowledged `Put` returns another value, so it never does.

**The premises.** The deployment: the two addresses distinct and valid, no connection, no listener
(`DistDeploy`, decidable but for the network's start); each machine's files as on disk (`FsInit`, in
`MemberFiles` and `ClientFiles`: `Robust`'s own initial-state premise does not give it at `etcdFsSem`), and
the member machine's data directory and WAL area empty (`MemberFiles`). Carried over from the
in-process `putget` (`Spec/.../examples/etcd/putget/Main.lean`) until discharged: `bootstrap`'s results
(`BootFacts`), the server's workload and environment premises (`authRecordsFit`, ...), Go's method sets of
the gRPC service values and `errors.As`'s target, the member's named Iris premises (`Hprem`: the
trust-boundary contracts `bootstrapContract`, `bootMarshal`, the raft wrapper's, at every ghost-state
instance, as the retired single-process `etcd_safe`'s `Hprem`), `context`'s two classes (`Hctx`,
`Hcec`) (no premise on the programs' metric names, `HNs`, since prom-registry, 2026-11-23: each
machine's boot proof allocates its registration rights itself). `ETCD_VERIFY` (etcd's runtime checks, which panic outside
the apply loop) is off on every machine's run, as in the single-process theorems (`HEnv`: `verifyEnvOff`
of each machine's program, `Proof/go_etcd_io/etcd/client/pkg/v3/verify/Env.lean`), and `HEnvTok` is that
fact's token in the logic (`envVerifyOff`): in one process the start axiom `goose_adequacy_start` hands it
out under `verifyEnvOff`; a distributed start has no such axiom, so it is a premise here (the owner's
decision, 2026-11-23; no new axiom). No proxy premise yet: no verified step reads the proxy variables
before phase 7 S5's HTTP client (`notes/putget-dist-plan.md`, section 11).

**The step bound** is `2 ^ 28 - 1`, not the single-process theorems' `2 ^ 40 - 11`: Perennial's distributed
adequacy (`goose_dist_adequacy`) bounds the threads over every execution of `n` steps, which the bridge meets
with `n + 2` threads, and the server's specs take `threadBound ≤ 2 ^ 28`; an along-the-execution form, as
the single-process `goose_adequacy_below`, would restore the larger bound (`notes/perennial-changes.md`,
2026-11-23).

**What the semantics assumes** (not premises): the file extension at `etcdFsSem` (no file system call
fails, on the member's machine); the request ids' issue record keyed by heap address (sound here: no
machine crashes).

**Trusted gap**: the binaries (`cmd/{member,client}`) pass their arguments to `Member`/`Client`; the
parsing is not translated, so the boot programs are the functions applied to the addresses' Go strings.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.runtime.Start
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Init
public import Proof.log.NewModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Robustness go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- **`putget_safe`** (see the file header): the deployment of one member machine and one client machine,
neither of which crashes, is robust: no thread of either machine is stuck or has an unrecovered panic, so
the client's `Get` after an acknowledged `Put` returns the `Put`'s value. -/
def putget_safe.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    -- the deployment's addresses (the member's peer and client addresses)
    (peer client : GoString)
    -- bootstrap's results for the member's configuration (its id, its peers' contexts, its log)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : etcdstart.BootFacts id ctxs boot)
    -- the server's workload and environment (the in-process `putget`'s)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- the member's named premises, at every ghost-state instance (the single-process theorems')
    (Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcdstart.premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) name peer client n id ctxs
          boot)
    -- the machines' start states
    (σm σc : state) (g : GlobalState) (Hm : MemberFiles σm) (Hc : ClientFiles σc)
    (Hd : Net.DistDeploy (addrs peer client) (system peer client σm σc) g)
    -- `ETCD_VERIFY` off on every machine's run, and its token in the logic
    (HEnv : ∀ m ∈ system peer client σm σc, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := putgetGF)),
    Robust [] (system peer client σm σc) g (threads := 2 ^ 28) (bound := 2 ^ 28 - 1)

end etcd_putget_dist
end EtcdGrove
end Perennial

end
