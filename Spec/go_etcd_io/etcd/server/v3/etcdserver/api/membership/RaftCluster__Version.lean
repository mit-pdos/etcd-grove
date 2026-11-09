/-
## `(*RaftCluster).Version()` (`cluster.go:580-587`): trusted (names only)

**Users.** The lessor's `cluster` (3c: `lessor.shouldPersistCheckpoints`, `lessor.go:386`, on the
apply thread and the lessor's loop: `Lease.clusterOk` is this triple at the interface, which
`NewServer` (2d) proves for `srv.cluster` from this spec and `clusterVerInv`); 3a's
`applierV3backend.ClusterVersionSet` (the old version, for the downgrade check); the server's
`ClusterVersion()` getter and `monitorClusterVersions` (2d).

**Why it is true.** Under the mutex: `nil` if no version is set, else `semver.MustParse` of the
version's `String()`, a fresh `*Version` (`verFits`: it parses back, the view's `VerSt.ok` keeps
it). The update is a read (fired with the view unchanged).

**Changes**: new (verify-round, A8 completeness F3; lease-auth's request: `Lease.clusterOk` is the
`Version()` triple). **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- **The cluster version**: `nil` if none is set, else a fresh, read-only `*Version` holding it
(a read of the view, which keeps its versions fitting). -/
def RaftCluster.Version.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (Q : Option Semver.SemVer → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗
      (AU <{ ∃∃ (v : VerSt), clusterVer γ v ∗ ⌜v.ok⌝ }> @ ⊤, ∅ <{ clusterVer γ v, COMM Q v.ver }>) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Version")) (Val #()))
  {{ (p : Loc), RET #p; ∃ o : Option Semver.SemVer, Q o ∗
      ((⌜o = none ∧ p = null⌝) ∨ (∃ sv, ⌜o = some sv⌝ ∗ Semver.verAt p sv)) }}

end spec

end Membership
end EtcdGrove
end Perennial
