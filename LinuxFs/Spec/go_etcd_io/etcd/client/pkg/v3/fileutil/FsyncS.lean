/-
`fileutil.Fsync(f)` (sync_linux.go: `f.Sync()`) of a directory's `*os.File`, in the tree's shared mode:
`os.File.Sync.specDirS`'s triple (a shared directory fd; a success commits every entry the log had when
the caller knew its length, `osCommitLb n`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/FsyncS.lean`. Lean-first (W4: `syncDir`).
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Spec.os.File__SyncS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specDirS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (R : Roots) (j : Ino) (ph : DirPhS)
    (n : Nat),
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ os.ownFile (GF := GF) f fd name dqf ∗ osDirFdS fd j ph ∗
      osLogLb n }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync)) (Val #f))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osDirFdS fd j ph ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ osCommitLb n) }}

end spec

end EtcdGrove
end Perennial
