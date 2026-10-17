/-
`snap.Snapshotter.dbFilePath` (names-only here: no file-system model). Lean-first (no Rocq counterpart); etcd
PR #22046 (branch `pr-verify/etcd-22046`), for `(*snap.Snapshotter).SaveDBFrom`.
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

/-- `s.dbFilePath(id)` (names-only): the path of the snapshot database `id` (`snapDBPath s id`,
what `DBFilePath` returns), reading the snapshotter's `dir` field. -/
abbrev snap.Snapshotter.dbFilePath.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (dir : GoString) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      isSnapshotter s γ dir }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty
      @!! go!"dbFilePath")) (Val #id))
  {{ RET #(snapDBPath s id); True }}

end spec

end EtcdGrove
end Perennial
