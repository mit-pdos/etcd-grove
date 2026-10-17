/-
`(*snap.Snapshotter).DBFilePath(id)` (`server/etcdserver/api/snap/db.go`; names-only).
Lean-first (no Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
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

/-- `ss.DBFilePath(id)`: the path of the snapshot database `id` (`snapDBPath ss id`), or an
error (no such file, or the directory cannot be read). It reads the snapshotter's `dir` field
(set by `snap.New`, never written after) and lists the directory, which other goroutines may
change meanwhile (`SaveDBFrom`, `SaveSnap`, `ReleaseSnapDBs`); the spec says nothing about the
file's existence when the caller uses the path. (etcd PR #22046's branch adds the
snapshotter precondition: the method reads `ss.dir`, so it needs a snapshotter.) -/
abbrev snap.Snapshotter.DBFilePath.spec : Prop :=
  ∀ (ss : Loc) (γ : GName) (dir : GoString) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      isSnapshotter ss γ dir }}
    (App (Val (ss @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty
      @!! go!"DBFilePath")) (Val #id))
  {{ (p : GoString) (err : GoInterface), RET (PairV #p #err); fsResult err iprop(⌜p = snapDBPath ss id⌝) iprop(True) }}

end spec

end EtcdGrove
end Perennial
