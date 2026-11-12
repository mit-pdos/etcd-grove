/-
`(*leaseCache).delete` (`cache.go`), with the write lock held: a delete of a cached key (no
key-value, the header copied) if the header is not older. Changes: from `specs-ref`'s `leaseCache__delete.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.delete(key, hdr)` under the write lock. -/
def leaseCache.delete.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (key : GoString) (hdr : Loc) (dq : DFrac) (hm : HeaderM) (σ0 : State),
  {{ lcHeld (GF := GF) lc γ γL 1 ∗ respHeaderOwn hdr dq hm ∗ etcdLb γ σ0 ∗
      ⌜0 ≤ sint.Z hm.revision ∧ sint.Z hm.revision ≤ σ0.kv.rev⌝ ∗ lkvMarks γL (fun k => k = key) }}
    (App (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"delete")) (Val #key)) (Val #hdr))
  {{ RET #(); lcHeld lc γ γL 1 ∗ respHeaderOwn hdr dq hm }}

end spec

end Leasing
end EtcdGrove
end Perennial
