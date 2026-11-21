/-
**The member's data directory fits** (wal-fsfix, 2026-11-20, the user's decision: a bound on the
member's name): `memberDataDir name` is `dataBase/<name>.etcd`, so with a name of at most 200 bytes it
is a directory that fits (`Fs.DirFits`: under 3800 bytes, every 256-byte window holding a `/`), and
every path the server makes below it (`member/snap/db`, `member/snap/<16 hex>.snap.db`) fits
(`Fs.pathFits_of_dirFits` for one component; deeper ones by `Fs.winOk_child` a component at a time, with a length bound). Untrusted.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalLayout
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- `memberDataDir name` is `dataBase` with the component `<name>.etcd` below it. -/
theorem memberDataDir_child (name : GoString) :
    memberDataDir name = Fs.child dataBase (name ++ go!".etcd") := by
  simp only [memberDataDir, dataBase, Fs.child, List.append_assoc]
  rfl

/-- **A member name of at most 200 bytes gives a data directory that fits.** -/
theorem dirFits_memberDataDir (name : GoString) (h : name.length ≤ 200) :
    Fs.DirFits (memberDataDir name) := by
  rw [memberDataDir_child]
  have hb : (dataBase : GoString).length = 20 := by decide
  have he : (go!".etcd" : GoString).length = 5 := by decide
  refine ⟨?_, Fs.winOk_child (Fs.winOk_short (by omega)) ?_⟩
  · simp only [Fs.child, List.length_append, List.length_cons, List.length_nil, hb]; omega
  · simp only [List.length_append]; omega

/-- `srvWalDirOf (memberDataDir name)` is `walBase/<name>.etcd/wal`. -/
theorem srvWalDirOf_memberDataDir_child (name : GoString) :
    srvWalDirOf (memberDataDir name) =
      Fs.child (Fs.child walBase (name ++ go!".etcd")) go!"wal" := by
  rw [srvWalDirOf, walAreaOf_memberDataDir]
  simp [walBase, Fs.child, slashB]

/-- **A member name of at most 200 bytes gives a WAL directory that fits** (wal-fsfix2: `WalA.fits`, the
member's WAL area allocated at adequacy). -/
theorem dirFits_srvWalDirOf_memberDataDir (name : GoString) (h : name.length ≤ 200) :
    Fs.DirFits (srvWalDirOf (memberDataDir name)) := by
  rw [srvWalDirOf_memberDataDir_child]
  have hb : (walBase : GoString).length = 19 := by decide
  have he : (go!".etcd" : GoString).length = 5 := by decide
  have hw : (go!"wal" : GoString).length = 3 := by decide
  refine ⟨?_, Fs.winOk_child (Fs.winOk_child (Fs.winOk_short (by omega)) ?_) (by omega)⟩
  · simp only [Fs.child, List.length_append, List.length_cons, hb, he, hw]; omega
  · simp only [List.length_append]; omega

end EtcdGrove
end Perennial
