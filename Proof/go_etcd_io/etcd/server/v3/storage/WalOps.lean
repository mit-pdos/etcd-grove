/-
**The WAL's history operations** (moved out of `GooseLang/Ext/AbsDisk/Impl.lean`, wal-link Hm1 route (B),
2026-11-19, decided by etcd-grove-03): `WalOpG`, one `Save`/`SaveSnapshot` call's records, the element of
every WAL history (`WalHist`, `WalDur.H`), and the injective encodings of it and of the raft models it holds.
A pure move: the declarations keep their names.
-/
module

public import Proof.go_etcd_io.raft.v3.PbModel

@[expose] public section

noncomputable section

namespace Perennial

open go_etcd_io.raft.v3 EtcdGrove

/-- One WAL operation's records (CRC, metadata, cut-header and `Create`'s records omitted: the
reader ignores them, or they repeat a state, §1.3). `save h es`: `Save(h, es)` writes each entry's
record, then `h`'s unless `h` is empty (`saveState`, S/wal.go:1022-1030). `snap m`:
`SaveSnapshot(m)`, one record (its `ConfState` ignored: the reader reads index and term only). -/
inductive WalOpG (E : Type) where
  | save (h : HardStateM) (es : List E)
  | snap (m : SnapshotMetadataM)

/-! Injective encodings (the abstract disk's steps' arguments, `walCode`; the ghost state's values). -/

instance : Pos.Countable HardStateM :=
  .ofInjective (fun h => Pos.Countable.encode (h.Term', h.Vote', h.Commit'))
    (by intro a b h; cases a; cases b; simp_all)

instance : Pos.Countable ConfStateM :=
  .ofInjective (fun c => Pos.Countable.encode
      (c.Voters', c.Learners', c.VotersOutgoing', c.LearnersNext', c.AutoLeave'))
    (by intro a b h; cases a; cases b; simp_all)

instance : Pos.Countable SnapshotMetadataM :=
  .ofInjective (fun m => Pos.Countable.encode (m.ConfState', m.Index', m.Term'))
    (by intro a b h; cases a; cases b; simp_all)

instance {E : Type} [Pos.Countable E] : Pos.Countable (WalOpG E) :=
  .ofInjective (fun o => Pos.Countable.encode (match o with
      | .save h es => (Sum.inl (h, es) : (HardStateM × List E) ⊕ SnapshotMetadataM)
      | .snap m => Sum.inr m))
    (by intro a b h; cases a <;> cases b <;> simp_all)

end Perennial
