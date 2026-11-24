/-
`fileutil.OpenDir(path)` (dir_unix.go) as `OpenDir.lean`'s `spec`, with the error's
`fmtErrorOkOrNil` (its `Error()` returns a string): `wal.Open` wraps the error with `%w`
(S/wal.go:390-393, 2026-11-14). Proved in
`Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/OpenDirOk.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import Proof.os.NsS

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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.specOk : Prop :=
  ∀ (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R p dq j ∗
      osCallPerm (GF := GF) (callKey R p) qc }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir)) (Val #p))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R p dq j ∗ osCallPerm (callKey R p) qc ∗
      ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd p (DFrac.own 1) ∗
          osDirFdS fd j .idle) ∨
       ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }}

end spec

end EtcdGrove
end Perennial
