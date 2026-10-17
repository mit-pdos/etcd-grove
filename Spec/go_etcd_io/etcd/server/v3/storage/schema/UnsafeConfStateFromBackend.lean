/-
`schema.UnsafeConfStateFromBackend(lg, tx)` (`server/storage/schema/confstate.go`, translated
names-only). The trust boundary (etcd-io/etcd#19693's pr-verify, 2026-10-17). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvConfState.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `UnsafeConfStateFromBackend(lg, tx)`: `tx.UnsafeRange(Meta, MetaConfStateName, nil, 0)`; no
key, `nil`; one, its value decoded (`json.Unmarshal`) into a fresh `raftpb.ConfState`; more, a
panic (`lg.Panic`; excluded here, as is `Unmarshal`'s failure, `log.Panic`). The contents of the
returned conf state are not related to the stored bytes (`csRead`). -/
abbrev schema.UnsafeConfStateFromBackend.spec : Prop :=
  ∀ (lg : Loc) (r : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      csRangeOk r }}
    (App (App (Val (@! schema.UnsafeConfStateFromBackend)) (Val #lg)) (Val #(GoInterface.ok r)))
  {{ (cs : Loc), RET #cs; csRead cs }}

end spec

end EtcdGrove
end Perennial
