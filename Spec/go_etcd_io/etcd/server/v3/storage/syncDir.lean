/-
`storage.syncDir(dir)` (`server/storage/backend.go`, the fork's at pin e94f33b50: `OpenSnapshotBackend`'s
directory sync after the rename): the same code as `fileutil.syncDir` (`fileutil.OpenDir(dir)`,
`fileutil.Fsync`, `Close`), in the tree's shared mode: a spine to the directory `j` at `dir` (a
fraction) and a call permission fraction. **No error**: where the file system cannot fail on `dir`
(`FsNoErrOn (· = dir)`, which `theFs`'s `FsNoErrAll` gives for every path) and `dir` fits, the open
(`fileutil.OpenDir.specNE`), the sync (`Fsync.specDirS`, whose error needs `¬ FsNoErrIno`) and the close
(`os.File.Close.wp_dirSNE`) all succeed: `nil`, and every entry the log had when the caller knew its
length is committed (`osLogLb n` to `osCommitLb n`). (`OpenSnapshotBackend`'s caller,
`applySnapshot`, panics on the error, so the spec has none.) The file extension's instances are bound in the spec
(as `bbolt.Open.spec`'s), so that `OpenSnapshotBackend`, stated over the backend's `onFs` vocabulary,
calls it at `theFs`'s. Proved in `Proof/go_etcd_io/etcd/server/v3/storage/syncDir.lean`. Lean-first.
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.storage
-- `storage`'s `isPkgInit` (as `InvOpen.lean`), and its new imports' (`fileutil`, `path/filepath`)
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import Proof.path.filepath.PkgInit
public import Proof.os.NsS
public import Spec.os.StatAbove
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- See the file header. -/
abbrev storage.syncDir.spec : Prop :=
  ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
    (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) (n : Nat),
  FsNoErrOn (· = p) → PathFits p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R p dq j ∗
      osCallPerm (GF := GF) (callKey R p) qc ∗ osLogLb (GF := GF) n }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.syncDir)) (Val #p))
  {{ RET #GoInterface.nil; osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗ osCommitLb n }}

end spec

end EtcdGrove
end Perennial
