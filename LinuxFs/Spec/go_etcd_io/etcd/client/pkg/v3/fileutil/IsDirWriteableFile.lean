/-
`fileutil.IsDirWriteable(dir)` (fileutil.go:36-45) of a directory `J` whose `.touch` already holds a
regular file `i` (a leftover probe: a crash, or an earlier error, between its create and its remove):
`os.WriteFile` truncates it (`os.WriteFile.specTruncS`, which needs the file held whole: `trFile i
False`), then `os.Remove` unlinks it. As `IsDirWriteable.spec` otherwise: the caller holds `.touch`'s
claim whole; on success `.touch` holds nothing; on an error it holds nothing or the same file, never a
directory, and the file, if still there, is given back whole. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/IsDirWriteableFile.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import LinuxFs.Spec.os.WriteFileTrunc

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [os.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.specFile : Prop :=
  ∀ (dir : GoString) (R : Roots) (J i : Ino) (dq : DFrac) (hJ : NamesH) (qc : Qp),
  dir.length < 2 ^ 60 → hJ.cur !! go!".touch" = some (.file i) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ osInv (GF := GF) ∗
      osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R dir dq J ∗ osCallPerm (GF := GF) qc ∗
      osNames (GF := GF) J (.only [go!".touch"]) (DFrac.own 1) hJ ∗ trFile i False }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable)) (Val #dir))
  {{ (err : GoInterface), RET #err; osPathS R dir dq J ∗ osCallPerm qc ∗
      ∃ hJ', osNames J (.only [go!".touch"]) (DFrac.own 1) hJ' ∗
        (⌜hJ'.cur !! go!".touch" = none⌝ ∨ ⌜hJ'.cur !! go!".touch" = some (.file i)⌝ ∗ trFile i False) ∗
        ⌜err = interface.nil → hJ'.cur !! go!".touch" = none⌝ }}

end spec

end EtcdGrove
end Perennial
