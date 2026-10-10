/-
`leaseCache.delete(key, hdr)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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

/-- **`lc.delete(key, hdr)`**, called with the write lock held: the delete at the header `h` is
applied to `key`'s entry, if any (`LeaseEntry.del`: if not older than the cached response, the
key-values are dropped and the header becomes a fresh copy `h'` of `h`). -/
abbrev leaseCache.delete.spec : Prop :=
  ∀ (lc : Loc) (st : LeaseCacheSt) (key : GoString) (h : Loc) (hm : HdrM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcOwn lc st (DFrac.own 1) ∗ ⌜LeaseCacheWf st⌝ ∗ hdrFull h hm }}
    (App (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"delete")) (Val #key)) (Val #h))
  {{ RET #(); ∃ h' : Loc, lcOwn lc (st.modify key (fun e => e.del h' hm)) (DFrac.own 1) }}

end spec

end leasing
end EtcdGrove
end Perennial
