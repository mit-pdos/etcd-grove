/-
`fileutil.TouchDirAll(lg, d)` over `fsExt` (W4/W13 of `notes/wal-fsext-plan.md`; the main tree's axiom
`Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAll.lean` restated over the tree's shared mode).
FU/ = `client/pkg/fileutil/fileutil.go` at the pin (F-N2: the parent's fsync in both branches). To be
proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAll.lean`. Lean-first.
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

/-- **`TouchDirAll(lg, d)`** (FU/fileutil.go:49-85), `d = parent/name`, `name` absent: the caller holds a
fraction of `parent`'s spine, the whole claim on `name` (holding nothing) and the whole call permission
(`mkdir` is a directory operation). `TouchDirAll` stats `d` (absent: an error), climbs while `Stat`
fails collecting the missing directories, `MkdirAll`s `d`, syncs the parent of each directory it
collected (outermost first; `d`'s parent last, F-N2), and probes `d/.touch` (`IsDirWriteable`). On
success `name` holds a new empty directory `J` (its whole claim), and every entry that wrote `name` is
committed (`osCommitLb n`, `h'.next ≤ n`): `d`'s entry survives any crash once `parent`'s does (the old
spec's `dirDurable d`, which the WAL layer derives from it). On an error, `name` holding nothing or a
directory of files, both claims whole (`tmpDirH`; until `wal-leaf4` the weaker `osSubtreeH`). Statement changes (sixth session): `name` absent (the os layer has no spec of a create
over an existing `.touch` nor of `MkdirAll`/`Stat` of an existing name whose subtree the caller holds
only as claims; `Create` removes a leftover `dir.tmp` first); `isPkgInit fileutil`; `d`'s length bound
(`filepath.Join`); the vacuous `("/", j0) ∈ R` premise dropped (`RootForm` excludes `/` as a root). -/
abbrev fileutil.TouchDirAll.spec : Prop :=
  ∀ (lg : Loc) (R : Roots) (jp : Ino) (d parent name : GoString) (qp : Qp) (h : NamesH),
  d = child parent name → NameOk name → d.length < 2 ^ 60 → h.cur !! name = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      zapLoggerOk (GF := GF) lg ∗ osInv ∗ osSharedInv R ∗ osPathS R parent (DFrac.own qp) jp ∗
      osCallPerm 1 ∗ osNames jp (.only [name]) (DFrac.own 1) h }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; osPathS R parent (DFrac.own qp) jp ∗ osCallPerm 1 ∗
      ((⌜err ≠ interface.nil⌝ ∗ ∃ h', tmpDirH jp name h') ∨
        (⌜err = interface.nil⌝ ∗ ∃ (h' hJ : NamesH) (J : Ino) (n : Nat),
          ⌜h'.cur !! name = some (.dir J) ∧ h'.next ≤ n ∧ hJ.cur = ∅⌝ ∗
          osNames jp (.only [name]) (DFrac.own 1) h' ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
          osCommitLb n)) }}

end spec

end EtcdGrove
end Perennial
