/-
`fileutil.IsDirWriteable(dir)` (fileutil.go:36-45): `filepath.Abs(filepath.Join(dir, ".touch"))`,
`os.WriteFile` of an empty file there, `os.Remove` of it, in the tree's shared mode. For a directory `J`
at `dir` (a spine to it, a fraction) whose name `.touch` holds nothing, the caller holding that name's
claim whole (`TouchDirAll`'s fresh directory: `MkdirAll` made it empty). On success `.touch` holds
nothing again (the create and the unlink logged); on an error, nothing or the probe file, never a
directory (so the caller's claims still cover `dir`'s subtree), the file given back whole (`trFile`;
`wal-leaf5`: a later probe truncates it, `IsDirWriteable.specFile`; until then the post dropped it). `dir`'s
length is bounded (`filepath.Join`'s premise). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/IsDirWriteable.lean`. Lean-first (W4).
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import LinuxFs.Proof.os.SharedAu
public import LinuxFs.Spec.os.OpenFileTruncS

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec : Prop :=
  ∀ (dir : GoString) (R : Roots) (J : Ino) (dq : DFrac) (hJ : NamesH) (qc : Qp),
  dir.length < 2 ^ 60 → hJ.cur !! go!".touch" = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ osInv (GF := GF) ∗
      osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R dir dq J ∗ osCallPerm (GF := GF) qc ∗
      osNames (GF := GF) J (.only [go!".touch"]) (DFrac.own 1) hJ }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable)) (Val #dir))
  {{ (err : GoInterface), RET #err; osPathS R dir dq J ∗ osCallPerm qc ∗
      ∃ hJ', osNames J (.only [go!".touch"]) (DFrac.own 1) hJ' ∗
        (⌜hJ'.cur !! go!".touch" = none⌝ ∨
          ∃ i, ⌜hJ'.cur !! go!".touch" = some (.file i)⌝ ∗ trFile i False) ∗
        ⌜err = interface.nil → hJ'.cur !! go!".touch" = none⌝ }}

end spec

end EtcdGrove
end Perennial
