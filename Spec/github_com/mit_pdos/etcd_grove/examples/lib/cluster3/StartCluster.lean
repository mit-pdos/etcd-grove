/-
`StartCluster(cfg, lg)` (`examples/lib/cluster3/cluster3.go`; until 2026-11-05 the members' and
bridges' part of package `partition`'s `startCluster`, at linkv3p's configuration; W4 of
`notes/watch-cut-plan.md`, 2026-10-22): the three members of configuration `cfg` started and served
(`StartMember`), and a bridge to each member's client address (`StartBridge`). Lean-first (no Rocq
counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the configuration's nine
addresses (and to serve the peer addresses with HTTP), the thread token, the cluster's named
premises (`premises`) and the members' WAL directories fresh, `StartCluster(cfg, lg)`, at a logger
`lg` (not null), returns the members, the bridges and `ok`: `false` (a step failed, nothing else
promised), or `true` with the thread token and the cluster up (`clusterUp`: every member at its
bridge with its watch registration, its KV or lease registrations by the lease mode (below), and its
place in the network, every bridge owned and not blackholed, and, in the mode `none`, etcd's KV at
the start store). The clients are the caller's (`NewClient`).

**The pure premises:** the configuration's (`cfgOk`), `bootstrap`'s results (`BootFacts`), and
`StartMember`'s.

**The lease mode** (lease-mono3, 2026-11-06, `notes/lease-mono3-plan.md`, Scope §1, §4 and Q4; hub
step 7's E2): the members' lessors in the mode `lm`, under the lease subsystem's premise at it
(`lease.runCfg lm lm`, `alloc1`'s and `alloc3`'s); `lm ≠ .revocable` is a scope premise of the
Scope's step 1 (§7: in the revocable mode the grant ids are collected at one prefix, `kvPfx`, which
is one member's; step 2 makes it the members' and removes the premise); the lease reads' deployment
premise `leasePeersOk` only in a mode that grants leases, so that no closed theorem at the mode
`none` gains a premise. The success is `clusterUp … lm`: in a mode that grants leases every member
registers the lease specs in place of the KV ones, and there is no client `etcdKV`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- See the file header. -/
abbrev StartCluster.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (lg : Loc) (cmp : Bool) (lm : lease.Mode),
  cfgOk cfg → BootFacts id₁ id₂ id₃ ps ctxs boot → lg ≠ null →
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  -- (lease-mono3) the lease mode: the subsystem's premise at it, not revocable (a scope premise,
  -- see the file header), and the lease reads' deployment premise in a mode that grants leases
  lease.runCfg (GF := GF) lm lm → lm ≠ .revocable → (lm ≠ .none → leasePeersOk) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 ∗
      -- (2026-11-05, hub step 7's E2, D1) the cluster's start bundle: each member's (its WAL
      -- directory fresh, its peer and client addresses free, the peer's HTTP protocol unregistered)
      -- and the bridges' addresses free
      startRes (GF := GF) cfg ∗
      threadTok ∗ premises cfg N id₁ id₂ id₃ ps ctxs boot }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartCluster))
      (Val #cfg)) (Val #lg))
  {{ (srvs brs : GoSlice) (ok : Bool), RET (PairV (PairV #srvs #brs) #ok);
      ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ threadTok ∗ clusterUp cfg cmp id₁ id₂ id₃ (LogEntry.toEntries boot 0) srvs brs lm) }}

end spec

end cluster3
end EtcdGrove
end Perennial
