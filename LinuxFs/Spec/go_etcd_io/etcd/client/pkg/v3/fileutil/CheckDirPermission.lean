/-
`fileutil.CheckDirPermission(dir, perm)` (fileutil.go:126-141): `Exist(dir)` (an error naming the
directory if not), `os.Stat(dir)` (its error returned), and an error naming both modes if the
directory's permission bits (`Mode().Perm()`) are not `perm`; `nil` otherwise. In the tree's shared
mode, `dir` the directory `J` (a spine to it, a fraction) and a fraction of the call permission: no
effect, some error (`TouchDirAll`, its one caller, only logs it). Over the part's `os.Stat` model
(`os.Stat.wp_dirS`: a `*fileStat` of some mode, or an error), `fileStat.Mode` and `FileMode.Perm`
(translated) and `fmt.ErrorfStrs.spec` (the `FileMode` arguments). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/CheckDirPermission.lean`. Lean-first
(`wal-leaf5`).
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import LinuxFs.Proof.os.SharedAu

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission.spec : Prop :=
  ∀ (p : GoString) (perm : w32) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ osInv (GF := GF) ∗
      osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R p dq J ∗ osCallPerm (GF := GF) qc }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission)) (Val #p)) (Val #perm))
  {{ (err : GoInterface), RET #err; osPathS R p dq J ∗ osCallPerm qc }}

end spec

end EtcdGrove
end Perennial
