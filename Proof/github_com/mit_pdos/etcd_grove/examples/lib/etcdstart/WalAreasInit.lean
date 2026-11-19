/- Lean-first (no Rocq counterpart).

# The closed theorems' premise on the members' WAL areas (wal-link P2, 2026-11-19)

`etcdWalAreasInit`, moved out of `WalAreas.lean` (which allocates the areas at adequacy) so that the
top-level robustness statements (`Spec/.../TopLevelRobustness.lean`) state it without importing the
allocation's proof (merge of lean 5f94c44bee, 2026-11-19). A premise of the closed theorems on the
file extension's initial state (a world premise, as `dataDirsAbsent`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalLayout
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section premise
variable [GooseExts]

/-- **The members' WAL areas and data directories exist at start, empty of what the members create** (a
premise of the closed theorems on the file extension's initial state `st`, a world premise as
`dataDirsAbsent`; wal-link P2; data directories 2026-11-19, approved by the user via etcd-grove-03:
`notes/datadir-relative-unsat.md`): each data directory `d` of `Ds` is a member's, `memberDataDir n`
(`/tmp/etcd-grove-data/<n>.etcd`); the path `walAreaOf d` (`/tmp/etcd-grove-wal/<n>.etcd`) is one of the
file extension's roots, a directory `j` with no entry at any name a WAL function may create, rename or
remove (`AreaSlot`: a WAL directory's name, no `.` or `/`, or such a name followed by `.` and anything;
so no WAL is found there and `wal.Create` finds its names free); and `d` itself is one of the roots, an
empty directory (the backend's and the snapshots' files are made there, `dataAreaFresh`). The examples'
Go tests make them so (each removed, then created empty, before the program runs: `walarea.Reset`).
Until 2026-11-19 the data directories were relative (`<n>.etcd`) and not in the premise. -/
def etcdWalAreasInit (st : Fs.OsState) (Ds : List GoString) : Prop :=
  ∀ d ∈ Ds, (∃ n, d = memberDataDir n) ∧
    (∃ j : Fs.Ino, (walAreaOf d, j) ∈ st.fs.roots ∧
      ∀ b, WalFs.AreaSlot b → st.fs.treeDur.entry j b = none) ∧
    (∃ j : Fs.Ino, (d, j) ∈ st.fs.roots ∧ ∀ b, st.fs.treeDur.entry j b = none)

end premise

end EtcdGrove
end Perennial

end
