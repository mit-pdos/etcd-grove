/-
`Cache.attachPrevKV(ctx, resp)` (`cache/cache.go`, new in etcd-io/etcd#21600). Lean-first (no
Rocq counterpart); see `InvCache.lean` (`prevKvOk`, `respPrevKvs`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.attachPrevKV(ctx, rp)`, by a reader of the store (`cacheReader`, given back), for a
response `*rp` modelled by `r` (`respAt`) whose events' `CreateRevision`s are readable
(`eventsCreateRevAt`): either `nil`, with `*rp` a response with the same model whose events
carry their `PrevKv` (`respPrevKvs`: each a fresh copy of the delivered event with `PrevKv` set,
or the delivered event itself for a create event); or a non-nil error whose `Error()` returns
some string (the context's, or the store lookup's wrapped by `fmt.Errorf`). The delivered
events are not written (they are shared with the other watchers). -/
abbrev Cache.attachPrevKV.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (rp : Loc)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗ context.isContext ctx s ∗ cacheReader cf ∗
      rp ↦ resp ∗ respAt resp r ∗ eventsCreateRevAt resp.Events' r.events }}
    (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"attachPrevKV"))
      (Val #(GoInterface.ok ctx))) (Val #rp))
  {{ (err : GoInterface), RET #err; cacheReader cf ∗
      ∃ resp' : go_etcd_io.etcd.client.v3.WatchResponse, rp ↦ resp' ∗
        ((⌜err = GoInterface.nil⌝ ∗ respAt resp' r ∗ respPrevKvs cf.pfx resp' r) ∨
         (∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e)) }}

end spec

end EtcdGrove
end Perennial
