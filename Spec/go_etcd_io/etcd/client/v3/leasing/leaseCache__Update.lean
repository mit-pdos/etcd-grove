/-
`leaseCache.Update(key, val, respHeader)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.Update(key, val, respHeader)`**, called with the write lock held (the caller owns the
state): the put of `val` to `key` at the header `h` (revision `hm.revision`) is applied to `key`'s
entry, if any (`LeaseEntry.update`: a fresh key-value if none was cached, the version bumped, the
value, mod revision and header set if the cached one is older). -/
abbrev leaseCache.Update.spec : Prop :=
  ∀ (lc : Loc) (st : LeaseCacheSt) (keySl : GoSlice) (key : GoString) (valSl : GoSlice)
    (val : GoString) (h : Loc) (hm : HdrM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcOwn lc st (DFrac.own 1) ∗ ⌜LeaseCacheWf st⌝ ∗ keySl ↦*□ key ∗ valSl ↦*□ val ∗
      hdrFull h hm }}
    (App (App (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"Update")) (Val #keySl)) (Val #valSl)) (Val #h))
  {{ RET #(); ∃ (p : Loc) (sl' : GoSlice),
      lcOwn lc (st.modify key (fun e => e.update (freshKv p keySl key hm.revision) sl' h hm valSl val))
        (DFrac.own 1) }}

end spec

end leasing
end EtcdGrove
end Perennial
