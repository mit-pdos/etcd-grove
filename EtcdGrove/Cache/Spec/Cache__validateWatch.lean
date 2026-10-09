/-
`Cache.validateWatch(key, op)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
import EtcdGrove.Cache.InvCache

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

/-- `c.validateWatch(key, op)`: a non-nil error if `op` asks for an unsupported option
(`watchUnsupported`); else `validateRange`'s error for the range `[key, op.RangeBytes())`;
else `nil` with the `KeyPredForRange` closure (`validateResult`). -/
abbrev Cache.validateWatch.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (key : GoString) (op : go_etcd_io.etcd.client.v3.Op) (o : OpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ opAt op o }}
    (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"validateWatch")) (Val #key)) (Val #op))
  {{ (f : GoFunc) (err : GoInterface), RET (PairV #f #err);
      validateResult o.watchUnsupported cf.pfx key o.rangeEnd f err }}

end spec

end EtcdGrove
end Perennial
