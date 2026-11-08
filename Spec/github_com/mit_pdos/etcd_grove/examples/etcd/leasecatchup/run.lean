/-
`run(lg)` (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3 step 1, 2026-11-06,
`notes/lease-mono3-plan.md`, Scope §2): `Main`'s body at the members' logger `lg`. It starts the
three-member cluster at `config()` (`cluster3.StartCluster`), a client of member 3's bridge and one
of member 1's (`etcdstart.NewClients`), grants a lease `g1` through member 3, cuts member 3 off the
two others (`cluster3.PeerStep`), grants up to 20 fillers through member 1 (the leader's log grows
and is compacted), mends the links, and polls member 3's listing until it lists the last filler;
then it panics unless that listing also lists `g1`. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the cluster's start bundle (`cluster3.startRes` at
`clusterCfg`: the members' WAL directories fresh, the nine addresses free), the thread token and
the cluster's named premises (`cluster3.premises` at `clusterCfg`), `run(lg)`, at a logger `lg`
(not null), returns (some `int`): it does not panic. The cluster runs in the monotone lease mode
(`StartCluster` at `.mono`), so member 3 registers the grant and the listing at its lessor's history
(`etcdLeaseGrantSpec`, `etcdLeaseLeasesSpec` of `(mvcc.api.mvccLeases E₃.γ)`, forwarded by its bridge): the grant's
reply carries `g1` granted at an index of member 3's lessor history (`leaseGrantedAt`), and any
listing of member 3 lists every lease granted there. That a listing still lists `g1` after member 3
has installed the leader's snapshot is the monotone lessor's (S2–S4's `Recover` premise, `mono → L ⊆
recs`, proved inside the server's apply loop): `run` itself does not reason about the catch-up.

**The pure premises** (in the precondition, the `⌜…⌝` conjuncts; review r1's SF5): `StartCluster`'s
(the bootstrap facts, `cluster3.BootFacts`; the thread and time-receipt bounds; the write budget;
the server's named workload and effect premises), at the monotone lease mode: no lease of any lessor
the program creates (granted, or reloaded by `Recover`) expires while the program runs
(`lease.leasesNoExpiry`, which gives `lease.runCfg .mono .mono`; leases are granted for an hour, the
run takes seconds) and the lease reads' deployment premise (`leasePeersOk`); the client's context
premises (`ContextReadErrs`, `ContextErrsClient`, instances, and `errors.As`'s target), as
leasegrant's `Main`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- See the file header. -/
abbrev run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup ∗
      cluster3.startRes (GF := GF) clusterCfg ∗
      threadTok ∗ cluster3.premises clusterCfg N id₁ id₂ id₃ ps ctxs boot ∗
      ⌜cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot⌝ ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      ⌜threadBound GF ≤ 2 ^ 28 ∧ receiptBound GF ≤ 2 ^ 48 ∧ receiptBound GF ≤ N + 1 ∧
        N + 7 + bootWB ≤ backend.wbInit⌝ ∗
      ⌜ckptEffectsOk ∧ authRecordsFit ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ storage.diskOk⌝ ∗
      ⌜leasePeersOk ∧ lease.leasesNoExpiry⌝ ∗
      ⌜v3rpc.ServerMethodSets ∧ errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.run)) (Val #lg))
  {{ (r : w64), RET #r; True }}

end spec

end etcd_leasecatchup
end EtcdGrove
end Perennial
