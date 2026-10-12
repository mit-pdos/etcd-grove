/-
`leaseCache.EvictRange(key, end)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lc.EvictRange(key, end)`** (write lock): in the state `st` it found, if an entry is in the
range, **`key`'s** entry (if any) is removed and `key`'s revocation time set
(`LeaseCacheSt.evictRange`, at the last clock reading `t`): the code deletes `key`, not the
entries in range (a finding). -/
abbrev leaseCache.EvictRange.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (key e : GoString) (Q : LeaseCacheSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ lcPeek X Qr ∗
      (∀ (st : LeaseCacheSt) (t : time.Time), X st 1 ={⊤}=∗ X (st.evictRange key e t) 1 ∗ Q st) }}
    (App (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"EvictRange")) (Val #key)) (Val #e))
  {{ RET #(); ∃ st : LeaseCacheSt, □ Qr st ∗ Q st }}

end spec

end leasing
end EtcdGrove
end Perennial
