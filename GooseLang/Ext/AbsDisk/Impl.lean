/-
The abstract-disk extension of GooseLang [Trusted definitions!] (WAL W4a, 2026-11-11; the approved
W4 Draft's §1.1 and §1.6, `notes/decisions.md`, "WAL W4").

The durable state of etcd's write-ahead logs, one per directory, at the level of the records a
restart reads: the history of `Save`/`SaveSnapshot` calls (`WalOpG`), how much of it is synced, the
purge positions, and whether the directory's entry is durable. Its name is the path of the Go
package whose functions move it, `go.etcd.io/etcd/server/v3/storage/wal`: the WAL is names-only (its
functions' specs are axioms, `Spec/go_etcd_io/etcd/server/v3/storage/wal/`), and an axiomatized body
is read as one that performs this extension's steps (`AbsDiskStep`). No translated code reaches the
steps: only the WAL's axiomatized bodies and trusted models (the tester's `purgeRound`) perform them.
Rung 3 (bbolt) adds a `bolt` field to `AbsDiskState`.

**The world assumptions** the crash relation (`walCrash`, `walImg`) rests on (the user's decisions of
2026-11-11, `notes/decisions.md`, "WAL W3"; the Go evidence is the WAL tester under the
ptrace-recorded crash file system, kill, posix, ordered and kill-then-power-loss models):
* **The bare fsync(2) contract** for files and directories: once `fsync`/`fdatasync` of a file
  returns 0, its content and size as of the call are durable, truncates and fallocates included;
  a create, mkdir, rename or unlink in a directory `d` is durable once an `fsync(d)` returns after
  it (no journal ordering is assumed). etcd's fork at the pin makes the WAL's names durable with it
  (F-N1, F-N2, F-N4: `wal.tmp` synced before its rename, the parents of `TouchDirAll`'s
  directories, and at a write-mode `ReadAll` the WAL directory and its parent).
* **Unsynced bytes are arbitrary** after a power loss (any content, per byte), and a kill keeps
  exactly what was written (the page cache).
* **Rewriting a sector never corrupts bytes of it that were already synced** (a record appended
  into a partly written, synced sector leaves the synced part intact).
* **No CRC32-Castagnoli collision** on torn or arbitrary data: a record that was not written whole
  never passes the WAL's CRC chain.
Under them, what a restart decodes is a record-granular prefix of what was written that reaches the
last sync (F-Z makes a restart's read itself synced); an image outside that set fails the restart's
read (bootstrap's error, or `Fatal`), which every read spec allows.
-/
module

public import Perennial.GooseLang.Lang
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

/-- A raw entry: what an entry record holds (`raftpb.Entry`'s term, index, type, data). -/
structure WalEnt where
  term : w64
  index : w64
  typ : w32
  data : List w8

/-! Injective encodings (the steps' arguments, `walCode`; the ghost state's values). -/

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

instance : Pos.Countable WalEnt :=
  .ofInjective (fun e => Pos.Countable.encode (e.term, e.index, e.typ, e.data))
    (by intro a b h; cases a; cases b; simp_all)

/-- **The value naming a step's argument** (an operation, a mark, a position): an injective code
as a string of `encode a` zero bytes. Any injective code gives the same semantics up to renaming
the values; no translated code builds one (only the WAL's axiomatized bodies, which pass the
operation, mark or position their axiom names). -/
def walCode {A : Type} [Pos.Countable A] (a : A) : GoString :=
  List.replicate (Pos.Countable.encode a).toNat (0 : w8)

theorem walCode_inj {A : Type} [Pos.Countable A] {a b : A} (h : walCode a = walCode b) : a = b := by
  have h' := congrArg List.length h
  simp only [walCode, List.length_replicate] at h'
  exact Pos.encode_inj (Pos.Pos_toNat_inj h')

/-- **What a crash can leave of a WAL whose history is `H` with its first `n` operations synced**:
the first `j` operations (`n ≤ j ≤ |H|`), then possibly the first `k` entry records of operation `j`
when it is a `Save` (its state record, written last, lost). Power loss: P1, P4, P5 and the sector
assumption (notes/decisions.md "WAL W3"); a kill: the page cache, which holds a record-granular
prefix of what was written; a kill then a power loss: an image of an image (`walImg_trans`). An
image whose decodable records end below the mark (a sector garbled against the sector assumption, a
purge gap, C-P6) is not here: the restart's read then fails (bootstrap's error or `Fatal`), which
every read spec allows. -/
def walImg {E : Type} (H : List (WalOpG E)) (n : Nat) (I : List (WalOpG E)) : Prop :=
  ∃ j, n ≤ j ∧ j ≤ H.length ∧
    (I = H.take j ∨
     ∃ h es k, H[j]? = some (.save h es) ∧ k ≤ es.length ∧
       I = H.take j ++ [.save ⟨0, 0, 0⟩ (es.take k)])

/-- **The durable state of the WAL in one directory**. `H`: every `Save`/`SaveSnapshot` since
`Create`, across restarts (after a crash, the image the crash left). `m`: how many operations of `H`
are synced. `unl`: the records before position `unl` are in files the WAL holds no lock on
(`ReleaseLockTo`, and a restart's `Open`, which locks from the opened snapshot's file on). `pur`: the
records before position `pur` may have been deleted (a purge round ran while `unl` was that). `cut`:
the next restart reads from position `cut` on (chosen at a crash, `≤ pur`). `metadata`: `Create`'s
metadata. `named`: the WAL directory's entry, and its ancestors', are durable. `sized`: as today's
`walRecs` flag (WalRecs.lean), every entry record of a successful `Save` is the encoding of an entry
object of bounded size. -/
structure WalDur where
  H : List (WalOpG WalEnt)
  m : Nat
  unl : Nat
  pur : Nat
  cut : Nat
  metadata : List w8
  named : Bool
  sized : Bool

/-- The state of a WAL that `Create` has just renamed into place: no operation, nothing synced,
locked, nothing purged, its entry not yet durable, sized (no entry record). -/
def walDurFresh (md : List w8) : WalDur :=
  { H := [], m := 0, unl := 0, pur := 0, cut := 0, metadata := md, named := false, sized := true }

/-- The extension's state: the WAL directories (rung 3 adds `bolt : GMap GoString BoltDur`), and
the directories whose entries (and ancestors') are durable (`TouchDirAll`, F-N2). -/
structure AbsDiskState where
  wal : GMap GoString WalDur
  dirs : GSet GoString

instance : Inhabited AbsDiskState := ⟨⟨∅, ∅⟩⟩

/-- The abstract-disk extension. No values of its own, no global state. -/
@[reducible] def absDiskExt : GooseExt where
  name := "go.etcd.io/etcd/server/v3/storage/wal"
  Val := Empty
  LocalState := AbsDiskState
  GlobalState := Unit

/-- **The crash relation of one WAL directory** [trusted]: a WAL whose entry is not yet durable
(`Create` between its rename and the parent's fsync) may vanish; otherwise the history becomes an
image `I` at or past the mark, the mark stays (a kill keeps unsynced records unsynced; F-Z makes the
restart's read durable, `ReadAll`'s post), the next read's purged prefix is any `k ≤ pur`. -/
def walCrash (d : WalDur) (d' : Option WalDur) : Prop :=
  (d.named = false ∧ d' = none) ∨
  ∃ I k, walImg d.H d.m I ∧ k ≤ d.pur ∧
    d' = some { d with H := I, cut := k, named := true }
-- `named := true` in the second arm: a WAL that survived a crash with its entry exists on the disk,
-- so (F-N1/F-N2, and K-N's fix F-N4, pinned at b18c2d500) its entry is durable after the reboot.

section absDisk
variable [GooseExts] [GoGlobalContext]

/-- The WAL in `dir`'s state, updated by `f` (no change if there is none). -/
def absDiskUpd (s : AbsDiskState) (dir : GoString) (f : WalDur → WalDur) : AbsDiskState :=
  match s.wal !! dir with
  | some d => { s with wal := <[dir := f d]> s.wal }
  | none => s

/-- **The steps** [trusted] (§1.6): one external operation per abstract step, each returning `()`
and leaving the heap alone. `"WalCreate"` of `(dir, meta)` puts a fresh WAL where there was none;
`"WalNamed"` makes `dir`'s entry durable; `"WalAppend"` appends an operation (the one the calling
WAL function writes: its spec says which); `"WalSync"` raises the synced mark to a position at most
the history's length; `"WalUnlock"` raises `unl` (`ReleaseLockTo`, a restart's `Open`: the files
before a snapshot record's position); `"WalPurge"` raises `pur` to `unl` (a purge round);
`"WalUnsize"` clears `sized` (a `Save` of unsized entries); `"DirDurable"` of `d` records that `d`'s
entry and its ancestors' are durable (`TouchDirAll`). The operation, mark and position a step takes
are passed as the second component of the argument, by their code (`walCode`): the WAL
function's spec (an axiom) says which ones its body passes. -/
def AbsDiskStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (s : AbsDiskState)
    (_g : Unit) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (s' : AbsDiskState) (_g' : Unit) :
    Prop :=
  h' = h ∧ e' = Val (#()) ∧
  match op with
  | "WalCreate" => ∃ (dir : GoString) (md : List w8), v = PairV (#dir) (#md) ∧
      s.wal !! dir = none ∧ s' = { s with wal := <[dir := walDurFresh md]> s.wal }
  | "WalNamed" => ∃ dir : GoString, v = #dir ∧ s' = absDiskUpd s dir (fun d => { d with named := true })
  | "WalAppend" => ∃ (dir : GoString) (o : WalOpG WalEnt), v = PairV (#dir) (#(walCode o)) ∧
      s' = absDiskUpd s dir (fun d => { d with H := d.H ++ [o] })
  | "WalSync" => ∃ (dir : GoString) (n : Nat), v = PairV (#dir) (#(walCode n)) ∧
      (∀ d, s.wal !! dir = some d → n ≤ d.H.length) ∧
      s' = absDiskUpd s dir (fun d => { d with m := max d.m n })
  | "WalUnlock" => ∃ (dir : GoString) (p : Nat), v = PairV (#dir) (#(walCode p)) ∧
      s' = absDiskUpd s dir (fun d => { d with unl := max d.unl p })
  | "WalPurge" => ∃ dir : GoString, v = #dir ∧
      s' = absDiskUpd s dir (fun d => { d with pur := max d.pur d.unl })
  | "WalUnsize" => ∃ dir : GoString, v = #dir ∧
      s' = absDiskUpd s dir (fun d => { d with sized := false })
  | "DirDurable" => ∃ d : GoString, v = #d ∧ s' = { s with dirs := <[d := ()]> s.dirs }
  | _ => False

end absDisk

/-- The extension's semantics: its steps, and at a crash every WAL directory's `walCrash` (the
directories' durability kept; no WAL appears). -/
instance absDisk_semantics : ExtSemantics absDiskExt where
  step := AbsDiskStep
  crash s s' := s'.dirs = s.dirs ∧
    (∀ dir d, s.wal !! dir = some d → walCrash d (s'.wal !! dir)) ∧
    (∀ dir, s.wal !! dir = none → s'.wal !! dir = none)

end Perennial
