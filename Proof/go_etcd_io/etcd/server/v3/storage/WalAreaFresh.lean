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
`bootstrap` checks, or fails, itself). So a faithful `bootstrap`, given it, can call `Create` and build
the open WAL `wal.bootOk` gives. The closed
theorems allocate it once per member, at adequacy (`lib/etcdstart/WalAreas.lean`), from the per-member
`fsExt` root (`walAreaOf`) their premise `etcdWalAreasInit` says is present and holds no WAL name.
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

/-- The member's WAL directory is its area's `wal`. -/
theorem srvWalDirOf_inArea (dd : GoString) : WalFs.InArea (walAreaOf dd) (srvWalDirOf dd) go!"wal" :=
  ⟨by unfold walNameOk; decide, by simp [srvWalDirOf, List.append_assoc]⟩

end defs

end EtcdGrove
end Perennial
