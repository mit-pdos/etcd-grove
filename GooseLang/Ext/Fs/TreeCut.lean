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
  rename replacing a directory) had no other call of its root in flight from its `CallBegin` to its
  step: no entry of its root was logged meanwhile, and every later entry of its root began after it
  (the root's whole call permission). An entry's root is its tag, `tagOf ρ`, under a ghost map `ρ`
  from directories to roots (`RootTags`: a directory keeps its root, an entry writes only its root's
  directories). (The design's footprints `(J,*)` are replaced by this rule:
  `notes/wal-fsext-i2-design.md`, "Implementation log"; per root since `notes/wal-link-l4-fsext.md`.)

and `LogValid`: each file operation was applicable to the tree it was logged on (`OpOk`), and a
created file's inode was named in no earlier tree.

Then, for each root, a closed set keeps every entry of that root up to its last kept directory
operation, and after it only the root's file operations, per slot a prefix; the replay is a tree whose
every slot holds what it held right after the last kept operation writing it (`slotAfter`), whose
files were all named at some point of the run, and whose directories each were one of some tree of
the run (`closed_cut`; each root's part of the replay is that of one tree of the run, but different
roots' parts may be of different trees).
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

/-- The directory an operation acts in: its first slot's. -/
def MetaOp.dir : MetaOp → Ino
  | .create j .. => j
  | .mkdir j .. => j
  | .remove j .. => j
  | .rename j .. => j

/-- An entry's root tag, under the ghost map `ρ` from directories to the roots whose trees they are
in: its directory's. -/
def tagOf (ρ : Ino → GoString) (e : LogEntry) : GoString := ρ e.op.dir

/-- **Directory operations exclusive, per root**: every entry below `s0` (logged before the shared
mode began, when calls did not overlap) began when it took effect, and every later entry's call
began after it; a directory operation had no entry of its root (`tagOf ρ`) logged from its call's
start to its step, and every later entry of its root began after it (the root's whole call
permission). Entries of other roots may overlap it: their directories are not its root's. -/
def DirOpExcl (ρ : Ino → GoString) (log : List LogEntry) (s0 : Nat) : Prop :=
  ∀ x (ex : LogEntry), log[x]? = some ex →
    (x < s0 → ex.start = x ∧ ∀ z (ez : LogEntry), x < z → log[z]? = some ez → x < ez.start) ∧
    (ex.op.IsDirOp →
      (∀ y (ey : LogEntry), ex.start ≤ y → y < x → log[y]? = some ey → tagOf ρ ey ≠ tagOf ρ ex) ∧
      ∀ z (ez : LogEntry), x < z → log[z]? = some ez → tagOf ρ ez = tagOf ρ ex → x < ez.start)

/-- The tree after the first `t` entries of `log`, replayed on `T0`. -/
def prefTree (T0 : Tree) (log : List LogEntry) (t : Nat) : Tree :=
  replay ((log.take t).map (·.op)) T0

/-- The directory `j` is reachable in `m` from the directory `ri` (a root's, for `Reach`). -/
inductive ReachFrom (m : Tree) (ri : Ino) : Ino → Prop where
  | root : ReachFrom m ri ri
  | child (j : Ino) (b : GoString) (j' : Ino) :
      ReachFrom m ri j → m.entry j b = some (.dir j') → ReachFrom m ri j'

/-- **The roots' tags**: `ρ` maps each root's directory to the root, a directory named by an entry
to its parent's root, in every tree of the run from `s0` on, and every directory an entry from `s0`
on writes to its directory's root (the entry's tag): a directory never changes root (a rename stays
in one root's tree), and entries of different roots write disjoint slots. -/
structure RootTags (ρ : Ino → GoString) (R : List (GoString × Ino)) (T0 : Tree) (log : List LogEntry)
    (s0 : Nat) : Prop where
  roots : ∀ r j, (r, j) ∈ R → ρ j = r
  ents : ∀ t, s0 ≤ t → t ≤ log.length → ∀ j b J,
    (prefTree T0 log t).entry j b = some (.dir J) → ρ J = ρ j
  ops : ∀ x (e : LogEntry), s0 ≤ x → log[x]? = some e → ∀ j b, e.op.Writes j b → ρ j = tagOf ρ e

/-- A file operation is applicable to the tree `m`: its directories exist, a create's name is
free, a removal's and a rename's source name what they record, a rename's target what it replaced.
-/
def OpOk (m : Tree) : MetaOp → Prop
  | .create j b _ => j ∈ m ∧ m.entry j b = none
  | .mkdir .. => True
  | .remove j b n => j ∈ m ∧ m.entry j b = some n
  | .rename j b j' b' n old => j ∈ m ∧ j' ∈ m ∧ m.entry j b = some n ∧ m.entry j' b' = old

/-- Each file operation of the log from `s0` on applicable to the tree it was logged on, and a
created file new: named in no earlier tree. -/
def LogValid (T0 : Tree) (log : List LogEntry) (s0 : Nat) : Prop :=
  ∀ x (e : LogEntry), log[x]? = some e → ¬ (e.op.IsDirOp ∨ x < s0) →
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

-- The consistent-cut theorem, `closed_cut`, is in `TreeCutProof.lean`.

end Fs
end Perennial

end
