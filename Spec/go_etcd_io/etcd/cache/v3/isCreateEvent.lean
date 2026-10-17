/-
`isCreateEvent(e)` (`cache/cache.go`, new in etcd-io/etcd#21600). Lean-first (no Rocq
counterpart); see `InvStore.lean` (`eventAt`) and `InvCache.lean` (`eventCreateRevAt`,
`isCreateModel`).
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

/-- `isCreateEvent(ev)`, for an event `ev` modelled by `e` (`eventAt`) with `CreateRevision`
`cr`: `e.Type == PUT && e.Kv.CreateRevision == e.Kv.ModRevision` (`isCreateModel`). -/
abbrev isCreateEvent.spec : Prop :=
  ∀ (ev : Loc) (e : EvModel) (cr : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ eventAt ev e ∗
      eventCreateRevAt e cr }}
    (App (Val (@! isCreateEvent)) (Val #ev))
  {{ RET #(isCreateModel e cr); True }}

end spec

end EtcdGrove
end Perennial
