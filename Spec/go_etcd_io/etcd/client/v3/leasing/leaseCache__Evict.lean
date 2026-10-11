/-
`leaseCache.Evict(key)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.Evict(key)`** (write lock): in the state `st` it found, `key`'s entry (if any) is removed
(frozen) and its revocation time set (`LeaseCacheSt.evict`, at a clock reading `t`); returns the
entry's revision (`0` if none). The client's step `Hstep` follows the transition. -/
abbrev leaseCache.Evict.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (key : GoString) (Q : LeaseCacheSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ lcPeek X Qr ∗
      (∀ (st : LeaseCacheSt) (t : time.Time), X st 1 ={⊤}=∗ X (st.evict key t) 1 ∗ Q st) }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"Evict")) (Val #key))
  {{ (r : w64), RET #r;
      ∃ st : LeaseCacheSt, ⌜r = st.revOf key⌝ ∗ entryFactsAt pfx key st ∗ □ Qr st ∗ Q st }}

end spec

end leasing
end EtcdGrove
end Perennial
