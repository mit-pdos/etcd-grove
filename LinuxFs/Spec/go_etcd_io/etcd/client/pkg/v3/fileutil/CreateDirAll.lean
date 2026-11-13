/-
`fileutil.CreateDirAll(lg, d)` over `fsExt` (W4/W13 of `notes/wal-fsext-plan.md`): `TouchDirAll`, then
`ReadDir(d)` must find it empty (FU/fileutil.go:103-117). To be proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/CreateDirAll.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
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

/-- **`CreateDirAll(lg, d)`**: `TouchDirAll`'s premises (`d = parent/name`, `name` absent, its claim
whole); on success `name` holds an empty directory `J` (its whole claim, nothing in it, is all the
subtree), every entry that wrote `name` committed; on an error, the subtree in some state. -/
abbrev fileutil.CreateDirAll.spec : Prop :=
  ∀ (lg : Loc) (R : Roots) (jp : Ino) (d parent name : GoString) (qp : Qp) (h : NamesH),
  d = child parent name → NameOk name → d.length < 2 ^ 60 → h.cur !! name = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      zapLoggerOk (GF := GF) lg ∗ osInv ∗ osSharedInv R ∗ osPathS R parent (DFrac.own qp) jp ∗
      osCallPerm 1 ∗ osNames jp (.only [name]) (DFrac.own 1) h }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; osPathS R parent (DFrac.own qp) jp ∗ osCallPerm 1 ∗
      ((⌜err ≠ interface.nil⌝ ∗ ∃ h', osSubtreeH jp name h') ∨
        (⌜err = interface.nil⌝ ∗ ∃ (h' hJ : NamesH) (J : Ino) (n : Nat),
          ⌜h'.cur !! name = some (.dir J) ∧ h'.next ≤ n ∧ hJ.cur = ∅⌝ ∗
          osNames jp (.only [name]) (DFrac.own 1) h' ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
          osCommitLb n)) }}

end spec

end EtcdGrove
end Perennial
