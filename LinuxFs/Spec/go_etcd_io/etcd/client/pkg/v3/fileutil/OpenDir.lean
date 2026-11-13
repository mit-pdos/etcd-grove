/-
`fileutil.OpenDir(path)` (dir_unix.go): `os.Open(path)` of a directory, in the tree's shared mode:
`os.Open.wp_dirS`'s triple (a shared directory fd, idle, on the directory `j` at `path`). `Open` keeps
it as `w.dirFile` (S/wal.go:394). Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/OpenDir.lean`.
Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.os.NsS
public import LinuxFs.Spec.os.StatAbove

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.spec : Prop :=
  ∀ (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp),
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R p dq j ∗
      osCallPerm (GF := GF) qc }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir)) (Val #p))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm qc ∗
      ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
          osDirFdS fd j .idle) ∨
       ⌜err ≠ interface.nil ∧ f = null⌝) }}

/-- `OpenDir(p)` of a strict ancestor of a root (`os.AboveRoot`): an fd of a directory outside the
roots' trees (`osOutFd`: only `Sync` and `Close` on it), or an error (2026-11-13, the extension's
`Open` outside case). -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.specAboveRoot : Prop :=
  ∀ (p : GoString) (R : Roots) (qc : Qp),
  os.AboveRoot R p →
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osCallPerm (GF := GF) qc }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir)) (Val #p))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osCallPerm qc ∗
      ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗ osOutFd fd) ∨
       ⌜err ≠ interface.nil ∧ f = null⌝) }}

end spec

end EtcdGrove
end Perennial
