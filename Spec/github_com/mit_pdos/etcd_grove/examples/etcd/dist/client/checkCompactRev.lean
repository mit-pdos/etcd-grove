/-
`checkCompactRev(cli, key)` (`examples/etcd/dist/client/compact.go`, compactwatch's): a watch of `key` from
revision 2, its first response's compaction revision (`etcdstart.CompactRev`), and, if it is a compaction's, a
latest `Get` of `key`, panicking if the `Get` reads below the compaction revision plus the retention (`1`).
Lean-first (no Rocq counterpart); #50 F5 (`notes/etcd-dist-plan.md` §26).

**The triple:** from `RunCompact`'s client of endpoints serving the cluster's view `Γ` (`isNewClient`, dialing
with no proxy, `membersAt`), the cluster's retention `1`, the KV invariant (`kvInv`: the compaction revision's
permit, a revision the cluster reached, bounds the later `Get`'s), compact's prefix and invariant with a fired
`key` under `cw/` and a lower bound `l0` of the history (what the watch's read update starts from), it returns
(it does not panic).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CompactWorkDefs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev checkCompactRev.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (key : GoString) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (γr : ServerRaftNames) (γ γF γh : GName) (σ₀ : KVState) (l0 : List (List mvcc.Change)),
  compactPfx <+: key → key.length ≤ 70 → Γ.kv.cret = 1 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ isNewClient cl eps V ∗ clientNoProxy cl ∗
      membersAt (Gg := hG.goose_globalGS) eps Γ ∗ kvInv (Gg := hG.goose_globalGS) γr Γ.kv ∗
      kvPfxH (Gg := hG.goose_globalGS) Γ.kv compactPfx γ cwOk γh σ₀ ∗
      cwInv (Gg := hG.goose_globalGS) γ γF ∗ cwFired (Gg := hG.goose_globalGS) γF key ∗
      monoListLbOwn γh l0 }}
    (App (App (Val (@! client.checkCompactRev)) (Val #cl)) (Val #key))
  {{ RET #(); levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
