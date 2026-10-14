/-
`Cache.Get(ctx, key, opts...)` (`cache/cache.go`): the end-to-end `Get` theorem. Lean-first (no
Rocq counterpart); see `InvCache.lean` and `InvEtcd.lean`.
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

/-- `c.Get(ctx, key, opts...)`, by a reader of the store (`cacheReader`, given back; `r0` a lower
bound on the store's revision the caller holds), with options whose closures have the model
transformers `gs` (`optsAt`; `OpGet` must not panic): for the request's `Op`
`o := (opGetModel key gs).base`, either `nil` and an error (`cacheGetErr`: the context, an
unsupported option, a range outside the prefix, the client's error, a future revision, a
timeout, or the store's error), or a fresh response with `nil` (`cacheGetOk`): the key-values
in `[key, o.rangeEnd)` of the cached snapshot `(r, m)` that `snapModel` picks for `o.rev`, where
`m` is etcd's state at `r` (`isEtcdKvs`), the header revision the store's latest revision
(`≥ r`, `snapModel_ok_spec`), and, unless the request is serializable, the store's latest
revision at least an etcd revision `serverRev ≥ o.rev` observed during the call. -/
abbrev Cache.Get.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat) (r0 : w64)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s ∗ optsAt sl gs ∗
      ⌜¬ opGetPanics gs⌝ ∗ cacheReader cf ∗ storeRevLb cf.γs r0 }}
    (App (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"Get"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      cacheReader cf ∗ cacheGetResult cf r0 s key (opGetModel key gs).base resp err }}

end spec

end EtcdGrove
end Perennial
