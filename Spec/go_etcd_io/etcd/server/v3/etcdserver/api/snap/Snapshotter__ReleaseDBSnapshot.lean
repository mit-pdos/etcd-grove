/-
`(*snap.Snapshotter).ReleaseDBSnapshot(id)` (`server/etcdserver/api/snap/db.go`, new in the PR).
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046` only). See
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

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

/-- `s.ReleaseDBSnapshot(id)`: atomically removes `id` from the pending set (a no-op if it is
not there). -/
abbrev snap.Snapshotter.ReleaseDBSnapshot.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (dir : GoString) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      isSnapshotter s γ dir }}
  <<{ ∀∀ M, snapPending γ M }>>
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty
      @!! go!"ReleaseDBSnapshot")) (Val #id)) @@ ∅
  <<{ snapPending γ (GMap.delete id M) }>>
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
