/-
`Main()` (`examples/etcd/lease/etcd_lease.go`; the closed lease example, 2026-11-02,
`notes/lease-ex-plan.md`): one etcd member started in process, a client connected to it, its
`Leases()` and `TimeToLive(7)`, and a panic if the listing has a lease twice or the answer is about
another lease. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23936` (`netAddrFree`, which program start gives once: D19d), the main thread's token
(`Start` forks the server's goroutines) and `Main`'s named premises (`etcd_lease.premises`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/lease/Defs.lean`), `Main()` returns: it does not
panic: the listing has no lease twice (etcd's `etcdLeaseLeasesSpecAny`, from the lessor's map's keys)
and the answer is about the lease asked (`etcdLeaseTTLSpec`), whatever the lessor holds.

**The pure premises:** the member id and bootstrap log Go computes (`etcd_lease.BootFacts`); the
logic's thread bound and the time-receipt bounds (the adequacy theorem's choices: `threadBound GF ≤
2 ^ 28`, `receiptBound GF ≤ 2 ^ 48` and `≤ N + 1`); the named workload and effect premises of the
server's construction (`ckptEffectsOk`, `authRecordsFit`,
`apply.backendUnderQuota`, `grpcRepliesFit`, `storage.diskOk`); the deployment's peers answering the
lease handler's path as etcd's lease handler does (`leasePeersOk`, which the follower path of
`TimeToLive` takes; true here: the member's peer address is not served); Go's method sets of the gRPC service values
(`v3rpc.ServerMethodSets`) and that `errors.As` takes `*rpctypes.EtcdError` as a target (both
discharged by the adequacy theorem, from the package assumptions).
The method-set facts of `*errorString` (`ErrorStringLeaf`, theorems of the package assumptions),
which make `io.EOF`'s package fact the server's `eofVar` (`v3rpc.eofVar_of_init`; until 2026-10-20, when Perennial's `io`
and `context` facts did not keep `EOF`'s value and `closedchan`'s invariant, the two named Props
`EofFromIoInit` and `ClosedchanFromContextInit` stood here). The proof
allocates the storage registry (D19r (B)); it is stated under the cache package's assumptions,
which the server's and the client's lemmas take (their files' section variables) although
`leasekv` does not import the cache.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.lease.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_lease

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.lease.Assumptions]

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
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.lease ∗
      -- (2026-11-05, hub step 7) the member's start bundle: its WAL directory fresh and the right
      -- to listen on its client address (`netAddrFree`, which program start gives once: D19d)
      etcdstart.memberStartRes (GF := GF) go!"leasekv" ⟨none, some go!"127.0.0.1:23936"⟩ ∗
      threadTok ∗ premises N id ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.lease.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_lease
end EtcdGrove
end Perennial
