/-
`fileutil.TouchDirAll(lg, d)` (FU/fileutil.go:49-85, the fork's F-N2), `d = parent/name`, of a `name`
already holding a directory `J` of files (`wal.Create`'s leftover `nm.tmp`, which its `Exist` missed or
its `RemoveAll` left: `fileutil.CreateDirAll.specTmp`): the caller holds `tmpDirH` (the claims on
`name` and on `J`'s names whole, `.touch`'s file if any), a fraction of `parent`'s spine, the whole call
permission. `TouchDirAll` asks `Exist(d)`: if it answers yes, `CheckDirPermission(d, 0700)` (its error
only logged), `syncDir(parent)`; if no (a `Stat` error), it climbs while `Exist` fails collecting the
paths, `MkdirAll(d)` (no effect: `os.MkdirAll.specDirS`) and syncs each collected path's parent; then the
probe `IsDirWriteable(d)` (`.touch` absent, `IsDirWriteable.spec`, or a leftover file, `specFile`). On
success `name` still holds `J` (its claim unchanged) and `J` holds files only, `.touch` none; on an error,
a `tmpDirH`. No commit bound (ledger 2026-11-14, "the commit bound on an existing directory"). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAllDir.lean`. Lean-first (`wal-leaf5`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TmpDir
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
abbrev fileutil.TouchDirAll.specDir : Prop :=
  ∀ (lg : Loc) (R : Roots) (jp : Ino) (d parent name : GoString) (qp : Qp) (h : NamesH) (J : Ino),
  d = child parent name → NameOk name → d.length < 2 ^ 60 → h.cur !! name = some (.dir J) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      zapLoggerOk (GF := GF) lg ∗ osInv ∗ osSharedInv R ∗ osPathS R parent (DFrac.own qp) jp ∗
      osCallPerm 1 ∗ tmpDirH jp name h }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; osPathS R parent (DFrac.own qp) jp ∗ osCallPerm 1 ∗
      ((⌜err ≠ interface.nil⌝ ∗ ∃ h', tmpDirH jp name h') ∨
        (⌜err = interface.nil⌝ ∗ ∃ hJ : NamesH,
          ⌜FilesOnly hJ.cur ∧ hJ.cur !! go!".touch" = none⌝ ∗
          osNames jp (.only [name]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ)) }}

end spec

end EtcdGrove
end Perennial
