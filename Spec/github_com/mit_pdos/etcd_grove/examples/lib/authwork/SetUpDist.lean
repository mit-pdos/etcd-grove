/-
`SetUp(cli)` (`examples/lib/authwork/authkv.go`) at the cluster view (F7 stage S4, step 2): the same Go
function as `SetUp.lean`'s, its calls going to members at other machines (`etcd_dist.authd`'s auth-on
contracts). Lean-first (no Rocq counterpart).

`SetUp` puts the keys of `setupKeys` (each in its own request-timeout context), then makes the eight
admin calls of `setupCalls` in one such context, returning `false` at the first that fails. The client
`cli` is anonymous (`principalOf cfg = none`): a KV client and an auth client of the view
(`userClientAt`, `authClientAt`, over the same endpoints and configuration), so a call's header has no
user and, the history's last state once enabled, no admin request of it is admitted. Its puts carry the
caller's persistent updates (`writeAuD` at `Γ.kv`, at the caller's lower bound `L₀` of the requested log),
and it holds the client's view of the auth history at the boot history (`authHistView Γ.kv
[srvAuthSt0]`), so the history's updates are `SetUp`'s alone. When `SetUp` returns `true`, the history is
frozen (`authHistFrozen`) at a lower bound `Lset` of the requested log whose auth state is `setupSt r`.
Unlike `SetUp.spec`, no member's published auth state nor a committed log is returned: at the view a
member's floor comes from a later barrier read (`KV_GetOn_dist`'s `authFloorD`), whose requested prefix
extends `Lset`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Checks
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist

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
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev SetUp.spec_dist : Prop :=
  ∀ [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [NetProtoGS] (cl api ap : Loc) (eps : List GoString) (V : client.WEnv GF)
    (Γ : etcd_dist.DistView) (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (L₀ : List EntryModel),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → etcd_dist.authd.principalOf cfg = none →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.authwork ∗ levelTok 0 ∗
      etcd_dist.authd.userClientAt cl api eps V Γ cfg ∗ etcd_dist.authd.authClientAt cl ap eps V Γ cfg ∗
      srvReqLogLb γR L₀ ∗
      iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
        etcd_dist.authd.writeAuD Γ.kv none (.put (putWireOf (opPutModel k go!"setup" []))) L₀
          (fun _ => iprop(True))) ∗
      authHistView Γ.kv [srvAuthSt0] }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.authwork.SetUp)) (Val #cl))
  {{ (ok : Bool), RET #ok; levelTok 0 ∗ (if ok then
        iprop(∃ (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat),
          authHistFrozen Γ.kv γz hs ∗ srvReqLogLb γR Lset ∗
          ⌜admStates Γ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog Γ.kv srvAuthSt0 Lset = setupSt r⌝)
      else iprop(True)) }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
