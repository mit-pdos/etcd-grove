/-
`Cache.serverRevision(ctx)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see
`InvCache.lean` and `InvEtcd.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.serverRevision(ctx)`: a count-only, limit-1 `Get` of the prefix (`"/"` for the root cache)
through `c.kv` (`isEtcdKV`): etcd's revision `r` at the response, a revision at which etcd had a
state, or `0` and the client's (non-nil) error. -/
abbrev Cache.serverRevision.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s }}
    (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"serverRevision")) (Val #(GoInterface.ok ctx)))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ m : KvMap, isEtcdKvs r cf.pfx m) ∨
      ⌜err ≠ GoInterface.nil ∧ r = W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
