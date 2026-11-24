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
such an execution) of fewer than `putgetSteps` (`2 ^ 48`) steps along which each machine keeps fewer than
`putgetThreads` (`2 ^ 28`) threads, **no thread of either machine is stuck or has an unrecovered panic** (`Robust`). The client
panics if the `Get` after an acknowledged `Put` returns another value, so it never does.

**The premises.** The deployment's addresses are any strings that Go strings can be (`Hlp`, `Hlc`: shorter than
`2 ^ 63 - 1` bytes, for `AddrOk`'s loop): the programs check them (`AddrOk`, the net extension's `addrOk`;
the member also that they differ) and return at once on a bad one, so their validity is not a premise. The
network's and the machines' net states at start (no connection, no listener) are `Robust`'s own
`extsInitGlobal`/`extsInitLocal`, so not premises either; each machine's files as on disk (`FsInit`, in
`MemberFiles` and `ClientFiles`: `Robust`'s own initial-state premise does not give it at `etcdFsSem`), and
the member machine's data directory and WAL area empty (`MemberFiles`). Carried over from the
in-process `putget` (`Spec/.../examples/etcd/putget/Main.lean`) until discharged: `bootstrap`'s results
(`BootFacts`), the server's workload and environment premises (`authRecordsFit`, ...), Go's method sets of
the gRPC service values and `errors.As`'s target, the member's named Iris premises (`Hprem`: the
trust-boundary contract `bootstrapContract`, at every ghost-state instance, as the retired
single-process `etcd_safe`'s `Hprem`; `bootMarshal` and the raft wrapper's contracts are axioms since
2026-11-24, `proto.MarshalBootConfChange.wp_proof`, `NewRaftLoggerZap.wp_proof`,
`contention.NewTimeoutDetector.wp_proof`), `context`'s two classes (`Hctx`,
`Hcec`). (prom-registry, 2026-11-23: no premise on the programs' metric names, `HNs`: each machine's
boot proof allocates its registration rights itself.)
`ETCD_VERIFY` (etcd's runtime checks, which panic outside
the apply loop) is off on every machine's run, as in the single-process theorems (`HEnv`: `verifyEnvOff`
of each machine's program, `Proof/go_etcd_io/etcd/client/pkg/v3/verify/Env.lean`), and `HEnvTok` is that
fact's token in the logic (`envVerifyOff`): in one process the start axiom `goose_adequacy_start` hands it
out under `verifyEnvOff`; a distributed start has no such axiom, so it is a premise here (the owner's
decision, 2026-11-23; no new axiom). No proxy premise: the client dials with `grpc.WithNoProxy()`
(`etcdstart.NewClients`, since 2026-11-24), so it ignores `HTTPS_PROXY`, and no other verified step
reads the proxy variables before phase 7 S5's HTTP client (`notes/putget-dist-plan.md`, sections 11
and 12).

**The bounds** (2026-11-24): both named (`TopLevelDefs.lean`). The thread bound is `putgetThreads = 2 ^ 28`, the bound the
member's server specs take (`threadBound ≤ 2 ^ 28`); it bounds the live threads along the execution
(`Robust`'s `threads`, through Perennial's `goose_dist_adequacy_below`), so it no longer caps the step
bound. The step bound is `putgetSteps = 2 ^ 48`, the single-process `etcd_all`'s: an execution of `n` steps is run at
`n + 1` receipts (the adequacy theorem's choice), and the member's start takes at most `2 ^ 48`
(`etcdstart.wp_StartServer1`'s `receiptBound GF ≤ 2 ^ 48`, the receipt bound of the server's request ids),
with its write-back budget and named premises at `2 ^ 48 - 1` (`Hprem` at `n + 1 ≤ 2 ^ 48`, as
`etcd_all`'s). (Until 2026-11-24 the bound was `2 ^ 28 - 1`: `goose_dist_adequacy` bounded the threads by
`n + 2`, so the step bound was the server specs' thread bound.)

**What the semantics assumes** (not premises): the file extension at `etcdFsSem` (no file system call
fails, on the member's machine); the request ids' issue record keyed by heap address (sound here: no
machine crashes).

**Trusted gap**: the binaries (`cmd/{member,client}`) pass their arguments to `Member`/`Client`; the
parsing is not translated, so the boot programs are the functions applied to the addresses' Go strings
(the client's result, which `cmd/client` only prints, discarded: `bootClient`).
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
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    -- `os`'s struct field steps (the single-process theorems' premise; `etcdstart`'s linked results take
    -- them since `NewStorage`'s contract is proved over the real WAL, wal-nostorageok)
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
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
    -- the member's named premises, at every ghost-state instance (the single-process theorems', at
    -- `etcd_all`'s range: `n + 1 ≤ putgetSteps`, the member's receipts less one)
    (Hprem : ∀ n : Nat, n + 1 ≤ putgetSteps → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcdstart.premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) name peer client n id ctxs
          boot)
    -- the machines' start states
    (σm σc : state) (g : GlobalState) (Hm : MemberFiles σm) (Hc : ClientFiles σc)
    -- the addresses' lengths, those of Go strings (their validity the programs check)
    (Hlp : peer.length + 1 < 2 ^ 63) (Hlc : client.length + 1 < 2 ^ 63)
    -- `ETCD_VERIFY` off on every machine's run, and its token in the logic
    (HEnv : ∀ m ∈ system peer client σm σc, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := putgetGF)),
    Robust [] (system peer client σm σc) g (threads := putgetThreads) (bound := putgetSteps)

end etcd_putget_dist
end EtcdGrove
end Perennial

end
