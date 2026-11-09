/-
## `checkVersionCompatibility(name, server, minCluster)`

**Users.** `checkClusterCompatibilityFromHeader`.

**Proof sketch.** `MustParse` of `version.Version` and `MinClusterVersion` (constants that parse), `compareMajorMinorVersion`, `fmt.Errorf`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Checks a remote's versions against the local ones: the local versions and `nil` or an error. -/
def checkVersionCompatibility.spec : Prop :=
  ∀ (name : GoString) (server minCluster : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ semverAt server ∗ semverAt minCluster }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkVersionCompatibility)) (Val #name)) (Val #server)) (Val #minCluster))
  {{ (ls lmc : Loc) (err : GoInterface), RET (PairV #ls (PairV #lmc #err)); semverAt ls ∗ semverAt lmc ∗ Http.errOk err }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
