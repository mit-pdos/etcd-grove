/-
`(*clientv3.Client).checkVersion` (`client/v3/client.go`).

Users: `newClient` (`RejectOldCluster`).

Proof sketch: per endpoint a goroutine (a wait group backed by the goroutines' completion) calling
`c.Status(ctx, e)` (the `Maintenance` field, `maintAt`'s `Status`), `semver.NewVersion` of the
reply's version and `minSupportedVersion()` (its `panic` unreachable: the package's version is in
its list, a constant fact), sending one result on a buffered channel of the endpoints' count; the
first error received is returned; `wg.Wait()`.

Changes: new (no old spec; `RejectOldCluster` was excluded).

Margin: the error's meaning is not stated.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.checkVersion()`: `nil` or an error. -/
def Client.checkVersion.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (dq : DFrac) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who ∗ clientReady c ∗ epsTok c dq eps ∗ ⌜eps ≠ []⌝ }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"checkVersion")) (Val #()))
  {{ (err : GoInterface), RET #err; epsTok c dq eps }}

end spec

end ClientV3
end EtcdGrove
end Perennial
