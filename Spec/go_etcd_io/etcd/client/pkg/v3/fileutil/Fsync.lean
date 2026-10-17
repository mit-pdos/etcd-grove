/-
`fileutil.Fsync(f)` (`client/pkg/fileutil/sync_linux.go`: `f.Sync()`, `fsync(2)`; names-only).
Lean-first (no Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`), see
`InvSnapshotBackend.lean`.
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

/-- `fileutil.Fsync(f)` of a handle of the directory `dir`, holding a pending rename of `src`
onto a path `dst` in `dir`: on success the rename's entry is durable (`fs.entryDurable src dst`);
on failure nothing is known of it (the pending rename is consumed: after an `fsync` error Linux
does not promise that a later `fsync` makes earlier changes durable). (The one use: `storage.syncSnapDir`. Syncing a directory makes every entry
renamed into it before the sync durable; this spec carries one.) -/
abbrev fileutil.Fsync.spec : Prop :=
  ∀ (f : Loc) (dir src dst : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      fs.dirHandle f dir ∗ fs.renamePending src dst ∗ ⌜fs.dirOf dst = dir⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync)) (Val #f))
  {{ (err : GoInterface), RET #err;
      fs.dirHandle f dir ∗ fsResult err (fs.entryDurable src dst) iprop(True) }}

end spec

end EtcdGrove
end Perennial
