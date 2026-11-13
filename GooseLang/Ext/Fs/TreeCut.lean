/-
What a crash keeps of a log whose calls overlap (`notes/wal-fsext-i2-design.md`, §4.3): the shared
mode's disciplines on the log, and the consistent-cut theorem `closed_cut`. Pure. Untrusted.

The semantics' crash (`Impl.lean`, `MachineCrash`) keeps a set `S` of the log's entries closed under
`Follows`. With overlapping calls, a closed set need not be a prefix, and without a discipline the
replay of the kept operations need not be a tree (`TreeWf`; the design's §4.3 counterexample: an
`rmdir` kept, the `unlink` it needed dropped). The shared mode's specs keep three disciplines:

* `Starts`: an entry's call began no later than it took effect (the semantics: `CallBegin` records
  the log's length, the step appends);
* `PerSlotSeq`: an entry writing a slot (a directory's name) began after every earlier entry writing
  that slot took effect (a claim's `h.next ≤ s`);
* `DirOpExcl`: an operation on the directory structure (`mkdir`, `rmdir`, a directory's rename, a
  rename replacing a directory) had no other call in flight from its `CallBegin` to its step: it
  began right when it took effect, and every later entry's call began after it (the whole call
  permission, `osCallPerm 1`). (The design's footprints `(J,*)` are replaced by this rule:
  `notes/wal-fsext-i2-design.md`, "Implementation log".)

and `LogValid`: each file operation was applicable to the tree it was logged on (`OpOk`), and a
created file's inode was named in no earlier tree.

Then a closed set keeps every entry up to its last kept directory operation, and after it only file
operations, per slot a prefix; the replay is a tree whose every slot holds what it held right after
the last kept operation writing it (`slotAfter`), whose files were all named at some point of the
run, and whose directories are those of one of the run's trees (`closed_cut`).
-/
module

public import GooseLang.Ext.Fs.Crash
public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-! ## Slots and the disciplines -/

/-- A slot: a directory's inode and a name in it. -/
abbrev Slot := Ino × GoString

/-- The slots an operation writes (the names it adds, removes or changes). -/
def MetaOp.slots : MetaOp → List Slot
  | .create j b _ => [(j, b)]
  | .mkdir j b _ => [(j, b)]
  | .remove j b _ => [(j, b)]
  | .rename j b j' b' _ _ => [(j, b), (j', b')]

/-- The operation writes the entry `b` of the directory `j`: one of its slots, or any name of the
directory it makes (which it makes empty). -/
def MetaOp.Writes (o : MetaOp) (j : Ino) (b : GoString) : Prop :=
  (j, b) ∈ o.slots ∨ ∃ j0 b0, o = .mkdir j0 b0 j

/-- An operation on the directory structure: it makes, removes or moves a directory, or replaces
one. The others (a file's create, removal, rename onto a file or nothing) are file operations. -/
def MetaOp.IsDirOp : MetaOp → Prop
  | .create .. => False
  | .mkdir .. => True
  | .remove _ _ n => ∃ J, n = .dir J
  | .rename _ _ _ _ n old => (∃ J, n = .dir J) ∨ ∃ J, old = some (.dir J)

/-- Every entry's call began no later than it took effect. -/
def Starts (log : List LogEntry) : Prop := ∀ x (e : LogEntry), log[x]? = some e → e.start ≤ x

/-- **Per-slot sequentiality**: an entry writing a slot began after every earlier entry writing it
took effect. -/
def PerSlotSeq (log : List LogEntry) : Prop :=
  ∀ x y (ex ey : LogEntry), y < x → log[x]? = some ex → log[y]? = some ey →
    (∃ sl ∈ ex.op.slots, sl ∈ ey.op.slots) → y < ex.start

/-- **Directory operations exclusive**: a directory operation began when it took effect (no entry
between its call's start and its step), and every later entry's call began after it. -/
def DirOpExcl (log : List LogEntry) : Prop :=
  ∀ x (ex : LogEntry), log[x]? = some ex → ex.op.IsDirOp →
    ex.start = x ∧ ∀ z (ez : LogEntry), x < z → log[z]? = some ez → x < ez.start

/-- The tree after the first `t` entries of `log`, replayed on `T0`. -/
def prefTree (T0 : Tree) (log : List LogEntry) (t : Nat) : Tree :=
  replay ((log.take t).map (·.op)) T0

/-- A file operation is applicable to the tree `m`: its directories exist, a create's name is
free, a removal's and a rename's source name what they record, a rename's target what it replaced.
-/
def OpOk (m : Tree) : MetaOp → Prop
  | .create j b _ => j ∈ m ∧ m.entry j b = none
  | .mkdir .. => True
  | .remove j b n => j ∈ m ∧ m.entry j b = some n
  | .rename j b j' b' n old => j ∈ m ∧ j' ∈ m ∧ m.entry j b = some n ∧ m.entry j' b' = old

/-- Each file operation of the log applicable to the tree it was logged on, and a created file new:
named in no earlier tree. -/
def LogValid (T0 : Tree) (log : List LogEntry) : Prop :=
  ∀ x (e : LogEntry), log[x]? = some e → ¬ e.op.IsDirOp →
    OpOk (prefTree T0 log x) e.op ∧
    ∀ j b i, e.op = .create j b i → ∀ t, t ≤ x → ¬ Named (prefTree T0 log t) i

/-! ## What a slot holds after a crash -/

open Classical in
/-- The last entry of `S` writing the entry `b` of the directory `j`. -/
def lastKept (log : List LogEntry) (S : Nat → Prop) (j : Ino) (b : GoString) : Option Nat :=
  ((List.range log.length).filter
    (fun x => decide (S x ∧ ∃ e, log[x]? = some e ∧ e.op.Writes j b))).getLast?

/-- What the entry `b` of the directory `j` holds right after the last entry of `S` writing it (as
it was at boot if none). -/
def slotAfter (T0 : Tree) (log : List LogEntry) (S : Nat → Prop) (j : Ino) (b : GoString) :
    Option Node :=
  match lastKept log S j b with
  | some x => (prefTree T0 log (x + 1)).entry j b
  | none => T0.entry j b

/-- **The consistent-cut theorem.** A log with the shared mode's disciplines, every tree of whose
run is a tree over the roots: what a crash keeping a closed set `S` replays is a tree; each slot as
right after its last kept writer; its files named somewhere in the run; its directories those of one
of the run's trees. -/
theorem closed_cut {R : List (GoString × Ino)} {T0 : Tree} {log : List LogEntry}
    (hst : Starts log) (hps : PerSlotSeq log) (hdx : DirOpExcl log) (hv : LogValid T0 log)
    (hwf : ∀ t, t ≤ log.length → TreeWf R (prefTree T0 log t))
    {S : Nat → Prop} (hS : ∀ x, S x → x < log.length) (hc : Closed log S) :
    TreeWf R (replay (keptOps log S) T0) ∧
    (∀ j b, (replay (keptOps log S) T0).entry j b = slotAfter T0 log S j b) ∧
    (∀ i, Named (replay (keptOps log S) T0) i → ∃ t, t ≤ log.length ∧ Named (prefTree T0 log t) i) ∧
    (∃ t, t ≤ log.length ∧ ∀ j, j ∈ replay (keptOps log S) T0 ↔ j ∈ prefTree T0 log t) := by
  sorry

end Fs
end Perennial

end
