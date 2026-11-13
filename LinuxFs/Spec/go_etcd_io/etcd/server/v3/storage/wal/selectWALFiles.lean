/-
`selectWALFiles(lg, dirpath, snap)` (S/wal.go:442-459): the WAL directory's names
(`readWALNames`), the position of the last one whose index is at most the snapshot's
(`searchIndex`), and the check that the sequence numbers from there increase by one (`isValidSeq`).
At the file-system level, as `readWALNames`: a fraction of a claim on names `N` of the directory,
whose `.wal` names are all in `N` and, where the directory has them, segment names
(`fmt.walNameStr`: `searchIndex`'s and `isValidSeq`'s `lg.Panic`s unreachable). For a WAL directory
of `walInv` both follow from `WalDirClaim` and the segments' names. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/selectWALFiles.lean`. W5 of
`notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNames
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.searchIndex
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.isValidSeq
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Fs

section pure
variable [GooseExts]

/-- **A directory's names `selectWALFiles` can read** (its claim on `N`, history `h`): every
`.wal` name is in `N`, and every one the directory has is a segment's name. -/
def WalDirNamesOk (N : NameSet) (h : NamesH) : Prop :=
  ∀ b, go!".wal" <:+ b → N.Mem b ∧ ((h.cur !! b).isSome → ∃ s i, b = fmt.walNameStr s i)

/-- **`selectWALFiles`' success**: the names `ws` (`readWALNames`'), the position `k` of the last
one whose index is at most `index`, the sequence numbers from there consecutive. -/
def WalSelected (N : NameSet) (h : NamesH) (index : w64) (ws : List GoString) (k : Nat) : Prop :=
  WalNamesOut N h ws ∧ walSearch (ws.map walNameIdx) index = some k ∧
    walSeqOk 0 ((ws.drop k).map walNameSeq) = true

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.spec : Prop :=
  ∀ (lg : Loc) (d : GoString) (sp : Loc) (s : w64 × w64) (R : Roots) (j : Ino) (dq : DFrac)
    (qc : Qp) (N : NameSet) (dqn : DFrac) (h : NamesH),
  WalDirNamesOk N h →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R d dq j ∗
      osCallPerm (GF := GF) qc ∗ osNames (GF := GF) j N dqn h ∗ walSnapIdTerm sp s }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles)) (Val #lg))
      (Val #d)) (Val #sp))
  {{ (r : GoSlice) (k : w64) (err : GoInterface), RET (PairV (PairV #r #k) #err);
      osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h ∗
      ((∃ ws : List GoString, ⌜err = interface.nil ∧ 0 ≤ sint.Z k ∧
          WalSelected N h s.1 ws (sint.nat k)⌝ ∗ r ↦* ws) ∨
       ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errOk e) }}

end spec

end EtcdGrove
end Perennial
