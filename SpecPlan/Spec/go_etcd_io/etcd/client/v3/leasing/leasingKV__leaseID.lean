/-
`(*leasingKV).leaseID` (`kv.go`): the current session's lease (`session` non-nil once ready).
Proof sketch: read lock; `Session.Lease()` (1d). Changes: from `specs-ref`'s `leasingKV__leaseID.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `leaseID()`, once a session is ready. -/
def leasingKV.leaseID.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ sessionReady γL ∗ threadTok }}
    (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"leaseID")) (Val #()))
  {{ (id : w64), RET #id; threadTok }}

end spec

end Leasing
end EtcdGrove
end Perennial
