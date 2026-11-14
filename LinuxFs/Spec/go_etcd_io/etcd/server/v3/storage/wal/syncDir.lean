/-
`wal.syncDir(dir)` (S/wal.go:316-327, the fork's: `Create`'s `dir.tmp` fsync, F-N1): the same code as
`fileutil.syncDir` (`OpenDir(dir)`, `Fsync`, `Close`), the same spec (shared mode, a spine to the
directory `j` at `dir`, a call permission fraction; a success commits every entry the log had when the
caller knew its length). Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/syncDir.lean`.
Lean-first (W4).
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import LinuxFs.Proof.os.NsS

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
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.syncDir.spec : Prop :=
  ∀ (p : GoString) (R : Roots) (j : Ino) (dq : DFrac) (qc : Qp) (n : Nat),
  {{ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R p dq j ∗
      osCallPerm (GF := GF) qc ∗ osLogLb (GF := GF) n }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.syncDir)) (Val #p))
  {{ (err : GoInterface), RET #err; osPathS R p dq j ∗ osCallPerm qc ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ osCommitLb n) }}

end spec

end EtcdGrove
end Perennial
