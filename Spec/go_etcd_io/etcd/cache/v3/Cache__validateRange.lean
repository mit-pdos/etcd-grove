/-
`Cache.validateRange(startKey, endKey)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.validateRange(startKey, endKey)`: `nil` iff the range is `validRange` for the cache's
prefix, else the value of `ErrKeyRangeInvalid` (`rangeErr`). The slices are only read. -/
abbrev Cache.validateRange.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (startSl endSl : GoSlice) (start end_ : GoString) (d1 d2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ startSl ↦*{d1} start ∗ endSl ↦*{d2} end_ }}
    (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"validateRange")) (Val #startSl)) (Val #endSl))
  {{ (err : GoInterface), RET #err;
      startSl ↦*{d1} start ∗ endSl ↦*{d2} end_ ∗ rangeErr cf.pfx start end_ err }}

end spec

end EtcdGrove
end Perennial
