/-
`(*EtcdServer).NewUberApplier()` (`server.go:1181-1200`): 3a's `apply.NewUberApplier` over the
options built from the server's fields (logger, KV, alarm store, auth store, lessor, cluster, the
server as raft status and snapshot server, the consistent indexer, the backend under `bemu`, the
transaction limits, the warning threshold).

**Users**: `NewServer` (step 6), `applySnapshot` (after the new backend is installed).

**Proof sketch**: read the fields (`srvNode`; `s.KV()` by `KV.spec` at `srvNode_kv`'s `s.kv ↦□`, re-review
RR2: no `isServer`, which neither caller holds; `bemu`'s read lock for `s.be`: the thread's token);
the options' persistent part (3a's `optsOk`) from the stores' handles (`srvStores_agree`'s
names, 3e's `kvOk`, 3c's `lessorOk` at `srvCfg`'s `mc`, 3d's `authOk`, 2e's membership), the
server's own handles from `applyLent_opts` at the lent `applyLent s γ`, the hooks' contracts
(`hooksOk`, the server's `getTxPostLockInsideApplyHook`, proved once over 4a's `hookRun`);
the exclusive part (`optsSt`) from `srvStores s σ`; `apply.NewUberApplier.spec`.

**Changes**: verify round (A7-provability F7, completeness F3, F6): new here (the old tree's
`EtcdServer__NewUberApplier.lean`); the handles 3a left provisional are introduced by
`applyLent_opts`.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`NewUberApplier()`**: the member's uber-applier at its configuration, its state machine the
stores' state `σ`, lent `applyLent s γ` per application. -/
def EtcdServer.NewUberApplier.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (mc : Apply.MemberCfg) (σ : EtcdModel.State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvCfg s mc ∗ srvStores s σ ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"NewUberApplier")) (Val #()))
  {{ (ua : GoInterface), RET #ua; threadTok ∗ ∃ γc : Membership.CNames,
      Apply.isUber ua mc γ.etcd γc (applyLent s γ) ∗ Apply.smAt ua σ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
