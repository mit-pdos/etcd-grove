/-
`store.Compact` (`kvstore.go`): compaction (2026-10-13, unit 5a; `notes/decisions.md`, "mvcc: compaction").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`s.Compact(trace, rev)`**: the API's contract at `*store` (`mvcc.api.KV.Compact.contract`,
`Spec/.../mvcc/Api.lean`; stage 2 of the mvcc API, 2026-11-06: the store's internal spec, with the
compaction right, replaced by the API's; its internal statement is `mvcc.store.Compact.core`,
`Proof/.../mvcc/Api/CmpCb.lean`). -/
abbrev mvcc.store.Compact.spec : Prop :=
  ∀ s : Loc, mvcc.api.KV.Compact.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec

end EtcdGrove
end Perennial
