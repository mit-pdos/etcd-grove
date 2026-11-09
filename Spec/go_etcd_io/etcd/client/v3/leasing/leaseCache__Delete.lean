/-
`(*leaseCache).Delete` (`cache.go`): `delete` under the write lock. Changes: from `specs-ref`'s `leaseCache__Delete.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `lc.Delete(key, hdr)`: the header (copied) at a revision reached, given back. -/
def leaseCache.Delete.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (key : GoString) (hdr : Loc) (dq : DFrac) (hm : HeaderM) (σ0 : State),
  {{ lcAt (GF := GF) lc γ γL ∗ respHeaderOwn hdr dq hm ∗ etcdLb γ σ0 ∗
      ⌜0 ≤ sint.Z hm.revision ∧ sint.Z hm.revision ≤ σ0.kv.rev⌝ }}
    (App (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"Delete")) (Val #key)) (Val #hdr))
  {{ RET #(); respHeaderOwn hdr dq hm }}

end spec

end Leasing
end EtcdGrove
end Perennial
