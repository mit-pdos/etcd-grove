/-
`(*snap.Snapshotter).DBFilePath(id)` (`server/etcdserver/api/snap/db.go`; names-only).
Lean-first (no Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ss.DBFilePath(id)`: some path, or an error (no such snapshot file). It reads only the
snapshotter's directory, which nothing writes after `snap.New`. -/
abbrev snap.Snapshotter.DBFilePath.spec : Prop :=
  ∀ (ss : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap }}
    (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty
      @!! go!"DBFilePath")) (Val #id))
  {{ (p : GoString) (err : GoInterface), RET (PairV #p #err); fsResult err iprop(True) iprop(True) }}

end spec

end EtcdGrove
end Perennial
