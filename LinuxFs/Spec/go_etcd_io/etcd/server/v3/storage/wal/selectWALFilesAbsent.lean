/-
`selectWALFiles(lg, d/b, snap)` (wal.go) of a missing WAL directory: `readWALNames` fails
(`readWALNames.specAbsent`) and the error comes back wrapped (`errOk`). `openAtIndex` of a WAL that does
not exist (W3/W5's gap 2, `notes/wal-fsext-plan.md`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/selectWALFilesAbsent.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNamesAbsent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.specAbsent : Prop :=
  ∀ (lg : Loc) (d b : GoString) (sp : Loc) (R : Roots) (j : Ino) (dq : DFrac)
    (qc : Qp) (N : NameSet) (dqn : DFrac) (h : NamesH),
  NameOk b → N.Mem b → h.cur !! b = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R d dq j ∗
      osCallPerm (GF := GF) qc ∗ osNames (GF := GF) j N dqn h }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles)) (Val #lg))
      (Val #(child d b))) (Val #sp))
  {{ (r : GoSlice) (k : w64) (err : GoInterface), RET (PairV (PairV #r #k) #err);
      osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h ∗
      ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e }}

end spec

end EtcdGrove
end Perennial

end
