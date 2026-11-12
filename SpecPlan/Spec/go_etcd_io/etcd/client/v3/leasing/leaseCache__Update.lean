/-
`(*leaseCache).Update` (`cache.go`), with the write lock held: a put of a cached key: version
incremented, value and mod revision set if newer (`issues/leasing-update-stale.md`). Proof sketch:
the entry's response owned in `lcHeld`; it stays `cachedRespOk` (key, one key-value, the header
reached), and `entryOk` by the key's mark (its record is no longer the store's). Changes: from `specs-ref`'s `leaseCache__Update.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.Update(key, val, hdr)` under the write lock: the key and value bytes and the header kept by
the cache (read-only), the header at a revision reached. -/
def leaseCache.Update.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (ksl vsl : GoSlice) (key v : GoString) (hdr : Loc) (hm : HeaderM) (σ0 : State),
  {{ lcHeld (GF := GF) lc γ γL 1 ∗ ksl ↦*□ key ∗ vsl ↦*□ v ∗ respHeaderOwn hdr DFrac.discard hm ∗
      etcdLb γ σ0 ∗ ⌜0 ≤ sint.Z hm.revision ∧ sint.Z hm.revision ≤ σ0.kv.rev⌝ ∗
      lkvMarks γL (fun k => k = key) }}
    (App (App (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"Update")) (Val #ksl)) (Val #vsl)) (Val #hdr))
  {{ RET #(); lcHeld lc γ γL 1 }}

end spec

end Leasing
end EtcdGrove
end Perennial
