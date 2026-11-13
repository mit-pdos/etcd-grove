/-
`fileutil.syncDir(dir)` (fileutil.go:93-104): `OpenDir(dir)`, `Fsync` of it, `Close`, in the tree's shared
mode, with a spine to the directory `j` at `dir` (a fraction) and a call permission fraction. A success
commits every entry the log had when the caller knew its length (`osLogLb n` to `osCommitLb n`): the
F-N2 parent fsync of `TouchDirAll`, `Create`'s `dir.tmp` fsync. The fd is closed on every path. Proved
in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/syncDir.lean`. Lean-first (W4).
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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.spec : Prop :=
  ∀ (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) (n : Nat),
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R p dq j ∗
      osCallPerm (GF := GF) qc ∗ osLogLb (GF := GF) n }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir)) (Val #p))
  {{ (err : GoInterface), RET #err; osPathS R p dq j ∗ osCallPerm qc ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ osCommitLb n) }}

/-- `syncDir(p)` of a strict ancestor of a root (`os.AboveRoot`): any error, nothing changed: `OpenDir`
gives an fd of a directory outside the roots' trees (the extension's `Open` outside case, 2026-11-13,
pending the user's review), whose `Sync` claims nothing. A hypothesis of `TouchDirAll`'s proof, whose
final loop syncs the parent of every directory its `Exist` loop found missing, the root's parent
included when `Stat` of the root failed. Proved: `syncDir.wp_proofAboveRoot`. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.specAboveRoot : Prop :=
  ∀ (p : GoString) (R : Roots) (qc : Qp),
  os.AboveRoot R p →
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osCallPerm (GF := GF) qc }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir)) (Val #p))
  {{ (err : GoInterface), RET #err; osCallPerm qc }}

end spec

end EtcdGrove
end Perennial
