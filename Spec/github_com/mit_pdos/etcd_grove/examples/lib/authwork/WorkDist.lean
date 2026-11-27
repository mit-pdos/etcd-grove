/-
`Work(cli, who)` (`examples/lib/authwork/authkv.go`) at the cluster view (F7 stage S9): the same Go function as
`Work.lean`'s, run by a principal's machine (`etcd_dist_client.principalOp`), its calls going to the members at
other machines (`etcd_dist.authd`'s auth-on contracts). Lean-first (no Rocq counterpart).

**The triple:** `Work` does not panic, for a principal `who` of the program (`principals`) on a client of one
endpoint `a` of the members' endpoints `addrs` (a KV client and a watch client of the view at `[a]`,
`userClientAt`, `watchClientAt`, with configuration `cfg`), whose principal (`principalOf cfg`) is anonymous or,
for `u` and `v`, `who` itself (`bad`'s and `anon`'s clients carry no user), given the principals' environment
`akDistEnv addrs Γ γR` (`AuthRunDefs.lean`: after the set-up froze the auth history, the KV and history
invariants, the frozen history, its committed prefix's lower bound and every endpoint's floor above it). The
post is `Work.spec`'s: not panicking is the workload's part of the auth result (every request the auth state
refuses `who` returned an error, every reply holds only keys `who` may read, every write keeps the history
invariant), here at the cluster view: each call's auth row is the `On_dist` contract's (`writeCheckedD`,
`readCheckedD`, `watchCheckedD`) at the member that served it, refuted at the frozen history.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthRunDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchClientDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Net go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.authwork.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev Work.spec_dist : Prop :=
  ∀ [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [NetProtoGS] (cl api w : Loc) (who a : GoString) (addrs : List GoString) (V : client.WEnv GF)
    (Γ : etcd_dist.DistView) (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames),
  who ∈ principals → a ∈ addrs → Γ.auth = true → (∀ x y : w64, Γ.au x = Γ.au y → x = y) →
  (etcd_dist.authd.principalOf cfg = none ∨
    (etcd_dist.authd.principalOf cfg = some who ∧ (who = go!"u" ∨ who = go!"v"))) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.authwork ∗ levelTok 0 ∗
      etcd_dist.authd.userClientAt cl api [a] V Γ cfg ∗ etcd_dist.watchClientAt cl w [a] V Γ ∗
      etcd_dist_client.akDistEnv addrs Γ γR }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.authwork.Work)) (Val #cl)) (Val #who))
  {{ RET #(); levelTok 0 }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
