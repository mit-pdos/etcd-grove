/-
`leaseCache.Delete(key, hdr)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.Delete(key, hdr)`** (write lock): `delete` in the state `st` it found. -/
abbrev leaseCache.Delete.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (key : GoString) (h : Loc) (hm : HdrM) (Q : LeaseCacheSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ lcPeek X Qr ∗ hdrFull h hm ∗
      (∀ (st : LeaseCacheSt) (h' : Loc),
        X st 1 ={⊤}=∗ X (st.modify key (fun e => e.del h' hm)) 1 ∗ Q st) }}
    (App (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"Delete")) (Val #key)) (Val #h))
  {{ RET #(); ∃ st : LeaseCacheSt, □ Qr st ∗ Q st }}

end spec

end leasing
end EtcdGrove
end Perennial
