/-
`leaseCache.Rev(key)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.Rev(key)`** (read lock): the revision of `key`'s entry (`0` if none) in the state `st`
it read, with the entry's facts and what the client learns of `st` (`Qr`). -/
abbrev leaseCache.Rev.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ leaseCacheReader lc γ pfx X ∗ lcPeek X Qr }}
    (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"Rev")) (Val #key))
  {{ (r : w64), RET #r; leaseCacheReader lc γ pfx X ∗
      ∃ st : LeaseCacheSt, ⌜r = st.revOf key⌝ ∗ entryFactsAt pfx key st ∗ □ Qr st }}

end spec

end leasing
end EtcdGrove
end Perennial
