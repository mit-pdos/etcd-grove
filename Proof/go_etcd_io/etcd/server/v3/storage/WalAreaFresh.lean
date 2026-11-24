/-
**A fresh WAL area: what a member's first start hands the WAL** (wal-link P2, 2026-11-19;
`notes/wal-link-scope.md` §3.4 P2, §6). Lean-first.

`walAreaFresh dir`: the area `a` (`WalA`: the file system's instances, the WAL ghost state, the I/O
set, the roots, the area `a.r` and its directory `a.jr`) whose WAL directory is `dir` (`r/wal`), with
what `wal.Create(lg, dir, md)` takes of the area (`Spec/.../storage/wal/Create.lean`): the area's
invariants (`walAreaOk`, at the server's marshaller `walSrvMr`), the area durable (`dirDurable`), its
spine, the program's part of it (`walAreaRes`), the whole call permission of its root, the generation's
free lock token, and no WAL in `dir` (`walAbsent`, from which `Create`'s update from the view `none`);
and the facts on the paths `Create` takes (`InArea`, `cleanAbsPath`; not `Create`'s bound on the
directory's length, `dir.length < 2 ^ 59`, which holds of every path Linux accepts and which a faithful
`bootstrap` checks, or fails, itself). (wal-fsfix2, 2026-11-20) The area `a` also carries the no-lock-error
instance (`a.satL`, `NoMapLockErr a.Sio`) and `Fs.DirFits dir` (`a.fits`; from the member's name of at most 200
bytes at the allocation, `dirFits_srvWalDirOf_memberDataDir`), and every path below its directory in `a.Sio` by path
(`a.covP`; the closed theorems' `allIo` covers every path). So a faithful `bootstrap`, given it, can call `Create` and build
the open WAL `wal.bootOk` gives. The closed
theorems allocate it once per member, at adequacy (`lib/etcdstart/WalAreas.lean`), from the per-member
`fsExt` root (`walAreaOf`) their premise `etcdWalAreasInit` says is present and holds no WAL name.

`dataAreaFresh d` (2026-11-19, approved by the user via etcd-grove-03: `notes/datadir-relative-unsat.md`):
the member's data directory `d`, a root of its own (absolute, `memberDataDir`), empty, with the whole of it in
the tree's shared mode: its spine, the whole call permission of its root, and the whole claim on its names,
none of which names an entry. What a faithful `bootstrap` makes the backend's and the snapshots' files of
(`bootOk`'s `Hpath`, `Hsfree`: their claims are in this root's tree, `config.backendPathOf d`). Allocated with
the WAL area (`etcdWalAreasInit`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalLayout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **A fresh WAL area whose WAL directory is `dir`** (see the file header). -/
def walAreaFresh (dir : GoString) : IProp GF :=
  iprop(∃ a : WalA GF, ⌜a.dir = dir ∧ WalFs.InArea a.r a.dir go!"wal" ∧ cleanAbsPath a.r⌝ ∗
    (letI := a.ext; letI := a.semOk; letI := a.has; letI := a.W
     iprop(WalFs.walAreaOk walCodec walSrvMr a.R a.jr a.r ∗ WalFs.dirDurable a.r ∗
      Fs.osPathS a.R a.r (DFrac.own 1) a.jr ∗ WalFs.walAreaRes a.jr ∗
      Fs.osCallPerm (Fs.callKey a.R a.r) 1 ∗ WalFs.walUnlockedTok ∗ WalFs.walAbsent a.dir)))

/-- **A fresh data directory `d`, a root of its own, wholly the caller's** (see the file header), at some
file-extension instances (the program's, `extsLocalStart`'s). -/
def dataAreaFresh (d : GoString) : IProp GF :=
  iprop(∃ (S : ExtSemantics Fs.fsExt) (ok : Fs.FsSemOk (S := S)) (has : HasExt Fs.fsExt) (R : Fs.Roots)
      (j : Fs.Ino) (h : Fs.NamesH),
    ⌜cleanAbsPath d ∧ ∀ b, h.cur !! b = none⌝ ∗
    (letI := S; letI := ok; letI := has
     iprop(Fs.osInv ∗ Fs.osSharedInv R ∗ Fs.osPathS R d (DFrac.own 1) j ∗
      Fs.osCallPerm (Fs.callKey R d) 1 ∗ Fs.osNames j (.except []) (DFrac.own 1) h)))

open Iris.ProofMode in
/-- **A fresh data directory holds no entry** (2026-11-24, why `wal.bootRes` needs no `dataDirFresh`):
the caller's whole claim on its names knows none of them to name an entry, so no backend file is at
`config.backendPathOf d`. -/
theorem dataAreaFresh_empty (d : GoString) :
    dataAreaFresh (GF := GF) d ⊢ ∃ h : Fs.NamesH, ⌜∀ b, h.cur !! b = none⌝ := by
  unfold dataAreaFresh
  iintro ⟨%S, %ok, %has, %R, %j, %h, %Hp, -⟩
  iexists h
  ipureintro
  exact Hp.2

/-- **A member's fresh areas** (2026-11-19): its WAL area, whose WAL directory is `srvWalDirOf d`, and its
data directory `d` (`dataAreaFresh`). -/
def memberAreasFresh (d : GoString) : IProp GF :=
  iprop(walAreaFresh (srvWalDirOf d) ∗ dataAreaFresh d)

/-- The member's WAL directory is its area's `wal`. -/
theorem srvWalDirOf_inArea (dd : GoString) : WalFs.InArea (walAreaOf dd) (srvWalDirOf dd) go!"wal" :=
  ⟨by unfold walNameOk; decide, by simp [srvWalDirOf, List.append_assoc]⟩

end defs

end EtcdGrove
end Perennial
