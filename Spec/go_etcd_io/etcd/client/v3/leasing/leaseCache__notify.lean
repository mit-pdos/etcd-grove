/-
`leaseCache.notify(key)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.notify(key)`** (read lock): `key`'s entry's `*leaseKey` and waiter channel in the state
`st` it read (with a witness that the `*leaseKey` was installed under `key`, a receive right on
the channel and the entry's facts), or `(nil, nil)`. -/
abbrev leaseCache.notify.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ leaseCacheReader lc γ pfx X ∗ lcPeek X Qr }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"notify")) (Val #key))
  {{ (li : Loc) (wc : GoChan), RET (PairV #li #wc); leaseCacheReader lc γ pfx X ∗
      ∃ st : LeaseCacheSt, □ Qr st ∗
        ((⌜st.entries !! key = none ∧ li = null ∧ wc = null⌝) ∨
         (∃ ent : LeaseEntry, ⌜st.entries !! key = some ent ∧ li = ent.li ∧ wc = ent.waitc ∧
            li ≠ null⌝ ∗ waitcOk wc ∗ leaseKeyInstalled γ key li ∗ entryFacts pfx key ent)) }}

end spec

end leasing
end EtcdGrove
end Perennial
