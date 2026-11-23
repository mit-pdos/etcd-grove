/-
`fileutil.TouchDirAll(lg, d)` of an **existing directory** `d` (claim #34, 2026-11-23: `bootstrap`'s
`TouchDirAll(cfg.DataDir)` on the data directory, a root; `notes/bootstrap-proof-plan.md` §7.3), beside
`TouchDirAll.spec` (an absent name). FU/ = `client/pkg/fileutil/fileutil.go` at the pin. Proved over the
Go body in `Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAllExisting.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`TouchDirAll(lg, d)` of the directory `J` at `d`** (FU/fileutil.go:49-85; a spine to it, a
fraction; a root or below one): the caller holds a fraction of the call permission and the whole claim
on `J`'s name `.touch`, which holds nothing. Go: `Exist(d)` (`Stat`, which may fail); if it answers
`true`, `CheckDirPermission` (a warning only) and `syncDir` of `d`'s parent (above the roots when `d` is a
root: `osAboveInv`); if `false`, the climb collecting the directories `Exist` misses (past the root,
`Stat` above it), `MkdirAll(d)` (nothing changes: `d` exists) and `syncDir` of each one's parent; then
the probe `d/.touch` (`IsDirWriteable`). The post is `IsDirWriteable`'s (an error one `fmt` formats, `fmtErrorOkOrNil`): `.touch` holds nothing on
success, and nothing or the probe file (given back whole) on an error. No durability is claimed (`d`'s
entry is not new). -/
abbrev fileutil.TouchDirAll.specExisting : Prop :=
  ∀ (lg : Loc) (R : Roots) (J : Ino) (d : GoString) (dq : DFrac) (qc : Qp) (hJ : NamesH),
  d.length < 2 ^ 60 → hJ.cur !! go!".touch" = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      zapLoggerOk (GF := GF) lg ∗ osInv ∗ osSharedInv R ∗ osAboveInv ∗ osPathS R d dq J ∗
      osCallPerm (callKey R d) qc ∗ osNames J (.only [go!".touch"]) (DFrac.own 1) hJ }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; fmtErrorOkOrNil err ∗ osPathS R d dq J ∗ osCallPerm (callKey R d) qc ∗
      ∃ hJ', osNames J (.only [go!".touch"]) (DFrac.own 1) hJ' ∗
        (⌜hJ'.cur !! go!".touch" = none⌝ ∨
          ∃ i, ⌜hJ'.cur !! go!".touch" = some (.file i)⌝ ∗ trFile i False) ∗
        ⌜err = interface.nil → hJ'.cur !! go!".touch" = none⌝ }}

end spec

end EtcdGrove
end Perennial
