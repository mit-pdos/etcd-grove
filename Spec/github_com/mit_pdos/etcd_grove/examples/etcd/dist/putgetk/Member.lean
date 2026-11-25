/-
`Member(i, peers, clients)` (`examples/etcd/dist/putgetk/putgetk.go`): member `i` of a new cluster, on a
machine of its own (`notes/putget-dist-plan.md` §13). Lean-first (no Rocq counterpart).

The program: unless `i < len(peers)` and `Valid(peers, clients)`, it returns at once; else the initial
cluster's map (member `j` named `Name(j)`, its one peer URL `http://peers[j]`), `etcdstart.StartMember` of
member `i` (its raft handler served on its peer address, the server started), `etcdstart.Serve` at
`clients[i]`, then `holdForever()`; it returns only when a step fails.

**The triple**, for any configuration (`peers`, `clients`) and any `i`: from the slices of the two lists,
the configuration's named premises (`premises`: the in-process `putgetN`'s, audited, at the configuration's
members and the ids etcd computes), `bootstrap`'s log facts, its machine's start (`ETCD_VERIFY` off, member
`i`'s WAL area and data directory fresh) and, **if the configuration is `cfgOk` and `i` a member**, its share
of the cluster's start (`memberShareK`: `etcdClusterStart`'s `memberStartShare` at S5's names `S5` and some
cluster names `c`, its client address set at the cluster's view `c.view`; `c` exists only when the start ran the
cluster's allocation, so it is inside the wand), `Member` returns (only on an error, or at once on an
invalid configuration: else it holds forever). The member's peer half (`StartMember` on a member machine)
is S5's: its proof takes `etcd_dist.StartMember_dist.spec S5` as a named hypothesis.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Perennial.TrustedCode.crypto.fips140

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev Member.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : Net.NetProtoGS]
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 28)]
    (S5 : etcd_dist.S5Draft (G := hG.goose_globalGS) GF)
    (peers clients : List GoString) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (i : Nat) (peersSl clientsSl : GoSlice),
  crypto.fips140.GodebugFips140Off →
  BootLogFacts (idsOf peers) ps ctxs boot →
  i < 2 ^ 64 →
  srvLevels (GF := GF) →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk ∗
      threadTok ∗ peersSl ↦* peers ∗ clientsSl ↦* clients ∗
      -- the configuration's named premises (`putgetN`'s)
      premises (2 ^ 28) peers clients ps ctxs boot ∗
      -- the machine's start
      ⌜EtcdVerifyOff⌝ ∗ memberAreasFresh (GF := GF) (memberDataDir (nameOf i)) ∗
      -- its share of the cluster's start, if the configuration is one the program runs
      (⌜cfgOk peers clients ∧ i < peers.length⌝ -∗ ∃ c : etcd_dist.ClusterNames,
        memberShareK (G := hG.goose_globalGS) S5 c peers clients ps ctxs boot i) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Member)) (Val #(W64 i))) (Val #peersSl)) (Val #clientsSl))
  {{ RET #(); True }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
