/-
`fileutil.ReadDir(d/b)` (read_dir.go), no option, of a name `b` holding nothing (a fraction of a claim
of `d`'s directory `j` on names containing it): `os.Open` fails (`os.Open.wp_absentS`), and the error
comes back (`fmtErrorOkOrNil`, as `ReadDir.spec`'s error arm). The WAL's `readWALNames` of a missing WAL
directory (W3/W5's gap 2, `notes/wal-fsext-plan.md`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDirAbsent.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import LinuxFs.Proof.os.NsAbsentS

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.specAbsent : Prop :=
  ∀ (d b : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) (N : NameSet) (dqn : DFrac)
    (h : NamesH),
  NameOk b → N.Mem b → h.cur !! b = none →
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      osPathS (GF := GF) R d dq j ∗ osCallPerm (GF := GF) qc ∗ osNames (GF := GF) j N dqn h }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir)) (Val #(child d b)))
      (Val #slice.nil))
  {{ (r : GoSlice) (err : GoInterface), RET (PairV #r #err); osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j N dqn h ∗ ⌜err ≠ interface.nil⌝ ∗ fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial

end
