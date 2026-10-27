/-
`startCluster(lg)` (`examples/linkv3p/linkv3p.go`; W4 of `notes/watch-cut-plan.md`, 2026-10-22):
`Main`'s start (until W4 inline in it): the three members started and served (`startMember`), a
bridge to each member's client address (`startBridge`), three clients each of every bridge
(`common.NewClients`, linkv3p's `newClient` until 2026-10-23; failover, D27). Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the nine addresses, the
thread token and `Main`'s named premises (`linkv3p.premises`), `startCluster(lg)`, at a logger
`lg` (not null), returns the members, the bridges, the clients and
`ok`: `false` (a step failed, nothing else promised), or `true` with the thread token and the
cluster up (`clusterUp`: every member at its bridge with its KV and watch registrations, every
bridge owned and not blackholed, every client `clientv3.New`'s over the three bridges at the
watch environment of the prefix `pfx`, the caller's choice, and etcd's KV at the start store).

**The pure premises:** `startMember`'s (`Main`'s but its bounds on `clients` and `ops`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev startCluster.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) (lg : Loc)
    (pfx : GoString),
  BootFacts id₁ id₂ id₃ ctxs boot →  lg ≠ null →
  threadBound GF ≤ 2 ^ 29 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  storage.dbOpensOk → v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      netAddrFree (GF := GF) peerAddr₁ ∗ netAddrFree (GF := GF) peerAddr₂ ∗
      netAddrFree (GF := GF) peerAddr₃ ∗ netAddrFree (GF := GF) clientAddr₁ ∗
      netAddrFree (GF := GF) clientAddr₂ ∗ netAddrFree (GF := GF) clientAddr₃ ∗
      netAddrFree (GF := GF) bridgeAddr₁ ∗ netAddrFree (GF := GF) bridgeAddr₂ ∗
      netAddrFree (GF := GF) bridgeAddr₃ ∗
      httpProtoFree (GF := GF) peerAddr₁ ∗ httpProtoFree (GF := GF) peerAddr₂ ∗
      httpProtoFree (GF := GF) peerAddr₃ ∗ threadTok ∗ premises N id₁ id₂ id₃ ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.startCluster)) (Val #lg))
  {{ (srvs brs clis : GoSlice) (ok : Bool), RET (PairV (PairV (PairV #srvs #brs) #clis) #ok);
      ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ threadTok ∗ clusterUp id₁ id₂ id₃ (Draft.LogEntry.toEntries boot 0) pfx srvs brs clis) }}

end spec

end linkv3p
end EtcdGrove
end Perennial
