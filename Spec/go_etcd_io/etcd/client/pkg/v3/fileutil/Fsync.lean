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

/-- `fileutil.Fsync(f)` of a handle of the directory `dir`, holding a pending rename onto a
path `dst` in `dir`: on success the rename's entry is durable (`fs.entryDurable dst`), on failure
it is still pending. (The one use: `storage.syncSnapDir`. Syncing a directory makes every entry
renamed into it before the sync durable; this spec carries one.) -/
abbrev fileutil.Fsync.spec : Prop :=
  ∀ (f : Loc) (dir dst : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      fs.dirHandle f dir ∗ fs.renamePending dst ∗ ⌜fs.dirOf dst = dir⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync)) (Val #f))
  {{ (err : GoInterface), RET #err;
      fs.dirHandle f dir ∗ fsResult err (fs.entryDurable dst) (fs.renamePending dst) }}

end spec

end EtcdGrove
end Perennial
