/-
`(*EtcdServer).revokeExpiredLeases(leases)` (`server.go:855-903`): in an attached goroutine, if this
member is (still) the leader, revoke each expired lease with `LeaseRevoke` under the root principal,
at most `maxPendingRevokes` at a time, each in an attached goroutine of its own.

**Users**: `run`'s expiry arm (`server.go:845`). Snippet `apply.go` (`ReqLeaseExpiry`).

**Proof sketch**. `s.GoAttach` (2e's wait group). `ensureLeadership()` (2c's: any answer is safe, the
revocation is idempotent at the model's level). For each lease: a slot of the buffered channel `c`
(or `s.stopping`); `s.GoAttach(func{ ... s.LeaseRevoke(authStore.WithRoot(s.ctx), {ID: lid}) ...
<-c })`. The update passed to 2c's `LeaseRevoke` (its spec takes the caller's update over
`etcdState γ.etcd`) is built from `envUpd γ.etcd γ.cfg` (in `srvNode`): at the revocation's commit,
a live lease `id` with its attached keys `l` steps by `Step root (.leaseRevoke id) σ (σ.revoke id l)
.ok`, which is `EnvStep.leaseExpire` (`γ.cfg.leaseExpiry = true`), so the environment's permission
fires it; a lease no longer live answers `ErrLeaseNotFound` with no change (an identity step,
nothing fired). This is K5's lease expiry: fired at the revocation entry's commit, the lease live.
Errors are logged.

**Changes** from `specs-ref`'s spec (the revoke-open premise, the reader slots): over `envUpd`;
the lease mode is the environment's (`γ.cfg.leaseExpiry`). **Margin**: none.
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

/-- **Revoke expired leases** (the lessor's report, in a cluster whose leases may expire). -/
def EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (γl : Lease.Names) (sl : GoSlice) (ids : List Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id ∗ srvLessor s γl ∗ Lease.expiredSl γl sl ids ∗ ⌜γ.cfg.leaseExpiry = true⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"revokeExpiredLeases")) (Val #sl))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
