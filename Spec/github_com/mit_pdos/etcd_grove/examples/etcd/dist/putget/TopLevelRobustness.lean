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
(`BootFacts`, and since 2026-11-24 `BootGo1`: the member id, its peers' contexts, its directory and
its log are Go's at the member's URLs), the server's workload and environment premises (`authRecordsFit`,
...), Go's method sets of the gRPC service values and `errors.As`'s target. The run's `fips140` GODEBUG
setting is unset or `off` (`Hfips`: with `only`, `crypto/sha1.Sum`, which computes the member id,
panics). No named Iris premise: `bootstrap`'s contract (`Hprem`, `bootstrapContract` at every
ghost-state instance, until 2026-11-24) is the interim axiom `bootstrap.wp_proofOne` (`bootstrap.spec`
at a one-member initial cluster of one URL; retired when #34 proves `bootstrap`); `bootMarshal` and the
raft wrapper's contracts are axioms since 2026-11-24, `proto.MarshalBootConfChange.wp_proof`,
`NewRaftLoggerZap.wp_proof`, `contention.NewTimeoutDetector.wp_proof`. (`context`'s two classes `Hctx`,
`Hcec` until ctx-leaf-fix, 2026-11-25: theorems since, `notes/axiom-review/ctx-readerrs-vacuity.md`; no
premise on the programs' metric names, `HNs`, since prom-registry, 2026-11-23: each machine's boot proof
allocates its registration rights itself.) `ETCD_VERIFY` (etcd's runtime checks, which panic outside
the apply loop) is off, as in the single-process theorems (`HEnv : EtcdVerifyOff`: the run's value of the
variable, one for every machine of the deployment, enables no check,
`Proof/go_etcd_io/etcd/client/pkg/v3/verify/Env.lean`; the owner's decision, 2026-11-25, which replaced
the per-machine axiomatized `verifyEnvOff` and its token premise `HEnvTok : ⊢ envVerifyOff`). No proxy
premise: the client dials with `grpc.WithNoProxy()` (`etcdstart.NewClients`, since 2026-11-24), so it
ignores `HTTPS_PROXY`, and no other verified step reads the proxy variables before phase 7 S5's HTTP
client (`notes/putget-dist-plan.md`, sections 11 and 12).

**The bounds** (2026-11-24): both named (`TopLevelDefs.lean`). The thread bound is `putgetThreads = 2 ^ 28`, the bound the
member's server specs take (`threadBound ≤ 2 ^ 28`); it bounds the live threads along the execution
(`Robust`'s `threads`, through Perennial's `goose_dist_adequacy_below`), so it no longer caps the step
bound. The step bound is `putgetSteps = 2 ^ 48`, the single-process `etcd_all`'s: an execution of `n` steps is run at
`n + 1` receipts (the adequacy theorem's choice), and the member's start takes at most `2 ^ 48`
(`etcdstart.wp_StartServer1`'s `receiptBound GF ≤ 2 ^ 48`, the receipt bound of the server's request ids),
with its write-back budget at `2 ^ 48 - 1`. (Until 2026-11-24 the bound was `2 ^ 28 - 1`: `goose_dist_adequacy` bounded the threads by
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
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootOne
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.runtime.Start
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
    [log.NewModel]
    -- `os`'s struct field steps (the single-process theorems' premise; `etcdstart`'s linked results take
    -- them since `NewStorage`'s contract is proved over the real WAL, wal-nostorageok)
    -- the deployment's addresses (the member's peer and client addresses)
    (peer client : GoString)
    -- bootstrap's results for the member's configuration (its id, its peers' contexts, its log)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : etcdstart.BootFacts id ctxs boot)
    -- the server's workload and environment (the in-process `putget`'s)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- (2026-11-24) `bootstrap`'s results for the member are Go's (its id, its peers' contexts, its log,
    -- at the member's URLs), and the run's `fips140` GODEBUG setting unset or off: the interim bootstrap
    -- axiom's pure premises (until then the named Iris premise `Hprem`, `bootstrap`'s contract)
    (Hbg : etcdstart.BootGo1 name peer client id ctxs boot) (Hfips : crypto.fips140.GodebugFips140Off)
    -- the machines' start states
    (σm σc : state) (g : GlobalState) (Hm : MemberFiles σm) (Hc : ClientFiles σc)
    -- the addresses' lengths, those of Go strings (their validity the programs check)
    (Hlp : peer.length + 1 < 2 ^ 63) (Hlc : client.length + 1 < 2 ^ 63)
    -- `ETCD_VERIFY` off (the deployment's value of the variable enables no check)
    (HEnv : EtcdVerifyOff),
    Robust [] (system peer client σm σc) g (threads := putgetThreads) (bound := putgetSteps)

end etcd_putget_dist
end EtcdGrove
end Perennial

end
