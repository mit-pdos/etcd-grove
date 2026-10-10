/-
`leaseCache.LockRange(begin, end)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lc.LockRange(begin, end)`** (write lock): in the state `st` it found, every entry in the
range (`leaseInRange`: `ks`, in the map's iteration order) gets a fresh waiter channel, returned
in that order, for the caller to close. -/
abbrev leaseCache.LockRange.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ lcPeek X Qr ∗ lcWaitcStep X }}
    (App (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"LockRange")) (Val #b)) (Val #e))
  {{ (sl : GoSlice), RET #sl;
      ∃ (st : LeaseCacheSt) (ks : List GoString) (cs : List GoChan),
        sl ↦* cs ∗ ownSliceCap GoChan sl (DFrac.own 1) ∗ ([∗list] c ∈ cs, waitcClose c) ∗
        □ Qr st ∗
        ⌜ks.Nodup ∧ (∀ k, k ∈ ks ↔ ∃ ent, st.entries !! k = some ent ∧ leaseInRange k b e = true) ∧
          cs.length = ks.length⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
