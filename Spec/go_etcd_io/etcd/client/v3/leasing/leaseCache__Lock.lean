/-
`leaseCache.Lock(key)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.Lock(key)`** (write lock): in the state `st` it found, if `key` has an entry, a fresh
waiter channel `wc` replaces the entry's (`LeaseCacheSt.setWaitc`) and is returned with the
entry's revision, for the caller to close (`waitcClose`); otherwise `(nil, 0)`. The client's
part of the invariant must not depend on waiter channels (`lcWaitcStep`). -/
abbrev leaseCache.Lock.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ lcPeek X Qr ∗ lcWaitcStep X }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"Lock")) (Val #key))
  {{ (wc : GoChan) (r : w64), RET (PairV #wc #r);
      ∃ st : LeaseCacheSt, ⌜r = st.revOf key⌝ ∗ entryFactsAt pfx key st ∗ □ Qr st ∗
        ((⌜st.entries !! key = none ∧ wc = null⌝) ∨
         (⌜(st.entries !! key).isSome = true⌝ ∗ waitcClose wc)) }}

end spec

end leasing
end EtcdGrove
end Perennial
