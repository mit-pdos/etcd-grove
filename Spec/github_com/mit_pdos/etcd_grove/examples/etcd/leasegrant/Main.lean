/-
`Main()` (`examples/etcd/leasegrant/etcd_leasegrant.go`; the closed lease-grant example, 2026-11-02,
`notes/lease-grant-plan.md`): one etcd member started in process, a client connected to it, its
`Grant(600)` and `Leases()`, and a panic unless the listing has the lease granted. Lean-first (no
Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23956` (`netAddrFree`, which program start gives once: D19d), the main thread's token
(`Start` forks the server's goroutines) and `Main`'s named premises (`etcd_leasegrant.premises`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/leasegrant/Defs.lean`), `Main()` returns: it does not
panic: the lease `Grant` returns was granted at an index of the lessor's history
(`etcdLeaseGrantSpec`), and `Leases()` lists every lease granted before it (`etcdLeaseLeasesSpec`:
the lessor of a cluster that grants leases is monotone).

**The pure premises:** as `leasekv`'s (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/lease/Main.lean`):
the member id and bootstrap log Go computes (`etcd_leasegrant.BootFacts`); the thread and time-receipt
bounds; the named workload and effect premises of the server's construction (`authRecordsFit`, `apply.backendUnderQuota`, `grpcRepliesFit`, `storage.diskOk`); the deployment's
peers answering the lease handler's path (`leasePeersOk`: the served Lease service's `TimeToLive`
handler takes it, `etcdstart.kv_lease_served`); **no lease the cluster grants expires while
the program runs** (`lease.leasesNoExpiry`, the lease-grant plan's S2 (a): the lease is granted for
600 s, the read that lists it runs within the request timeout; a deployment fact, not a fact of the
Go code: the lessor's expiry loop could revoke it; read also over the theorem's steps after `Main`
returns, which Go never takes: there it says the expiry loop never sends; `NewServer`'s gated
row takes it, `notes/lease-grant-plan.md`); Go's method sets of the gRPC service values and
`errors.As`'s target (both discharged by the adequacy theorem).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasegrant

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry),
  BootFacts id ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the server's gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk → lease.leasesNoExpiry →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant ∗
      -- (2026-11-05, hub step 7) the member's start bundle: its WAL directory fresh and the right
      -- to listen on its client address (`netAddrFree`, which program start gives once: D19d)
      etcdstart.memberStartRes (GF := GF) go!"leasegrant" ⟨none, some go!"127.0.0.1:23956"⟩ ∗
      threadTok ∗ premises N id ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_leasegrant
end EtcdGrove
end Perennial
