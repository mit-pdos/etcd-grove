/-
The pure part of the shared mode's region ghost state (`notes/wal-fsext-i2-design.md`, §2.2): name
sets (`NameSet`), what a claim on names knows of them (`NamesH`), a shared directory fd's phase
(`DirPhS`), and what a region concludes of a crash (`RegionCrashed`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeCut
public import GooseLang.Ext.Fs.TreeGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-! ## Name sets -/

/-- A set of names of a directory: finitely many, or all but finitely many. Two keys denoting the
same set are interchangeable (`osNames_rekey`). -/
inductive NameSet where
  | only (bs : List GoString)
  | except (bs : List GoString)
  deriving DecidableEq

/-- `b` is in the set. -/
def NameSet.Mem (N : NameSet) (b : GoString) : Prop :=
  match N with
  | .only bs => b ∈ bs
  | .except bs => b ∉ bs

/-- The names of `N` in `M` (a finite set). -/
def NameSet.inter (N : NameSet) (M : List GoString) : NameSet :=
  match N with
  | .only bs => .only (bs.filter (fun b => decide (b ∈ M)))
  | .except bs => .only (M.filter (fun b => decide (b ∉ bs)))

/-- The names of `N` not in `M` (a finite set). -/
def NameSet.diff (N : NameSet) (M : List GoString) : NameSet :=
  match N with
  | .only bs => .only (bs.filter (fun b => decide (b ∉ M)))
  | .except bs => .except (bs ++ M)

/-- The two sets have the same names. -/
def NameSet.Same (N N' : NameSet) : Prop := ∀ b, N.Mem b ↔ N'.Mem b

def NameSet.enc : NameSet → Bool × List GoString
  | .only bs => (true, bs)
  | .except bs => (false, bs)

instance NameSet.countable : Pos.Countable NameSet :=
  Pos.Countable.ofInjective (fun N => Pos.Countable.encode N.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [NameSet.enc])

open Classical in
/-- `e` restricted to the names of `N`. -/
def restrictN (N : NameSet) (e : Ents) : Ents :=
  GMap.filter (fun b _ => decide (N.Mem b)) e

/-! ## What a claim knows -/

/-- What a claim on the names `N` of a directory `j` knows of them: their entries in the tree the
generation's shared mode began with (`boot`), each logged entry writing one of them (its index, the
entry, and the names' entries right after it), and their entries now (`cur`). -/
structure NamesH where
  boot : Ents
  ents : List (Nat × LogEntry × Ents)
  cur : Ents

/-- The index after the last logged entry writing one of the names: a call that begins at a log
length at least this began after every such entry took effect. -/
def NamesH.next (h : NamesH) : Nat := (h.ents.getLast?.map (·.1 + 1)).getD 0

/-- The entry `e`, logged at `x`, recorded: the names' entries now `c`. -/
def NamesH.log (h : NamesH) (x : Nat) (e : LogEntry) (c : Ents) : NamesH :=
  { h with ents := h.ents ++ [(x, e, c)], cur := c }

open Classical in
/-- The history restricted to the names `M`. -/
def NamesH.restrict (h : NamesH) (j : Ino) (M : NameSet) : NamesH :=
  { boot := restrictN M h.boot,
    ents := (h.ents.filter (fun xe => decide (∃ b, M.Mem b ∧ xe.2.1.op.Writes j b))).map
      (fun xe => (xe.1, xe.2.1, restrictN M xe.2.2)),
    cur := restrictN M h.cur }

/-- A fresh claim: the names of `N`, as the tree `m`'s directory `j` has them, nothing logged. -/
def NamesH.init (m : Tree) (j : Ino) (N : NameSet) : NamesH :=
  ⟨restrictN N (entsOf m j), [], restrictN N (entsOf m j)⟩

instance NamesH.countable : Pos.Countable NamesH :=
  Pos.Countable.ofInjective (fun h => Pos.Countable.encode (h.boot, h.ents, h.cur))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)

open Classical in
/-- What the name `b` of the directory `j` holds after a crash keeping the entries `K`: as right
after the last kept entry writing it, as at boot if none. -/
def NamesH.valAfter (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) : Option Node :=
  match (h.ents.filter (fun xe => decide (K xe.1 ∧ xe.2.1.op.Writes j b))).getLast? with
  | some xe => xe.2.2 !! b
  | none => h.boot !! b

/-! ## What a region concludes of a crash -/

/-- A claim, as a region presents it: the directory, the names, the history. -/
abbrev Claim := Ino × NameSet × NamesH

/-- **What a region concludes of a crash** that left the tree `m'`, from its claims `cl` and a
lower bound `n` on the committed prefix: some set `K` of entries, closed under `Follows` among the
claims' entries (a kept entry keeps every claimed entry that took effect before it began),
containing every claimed entry below `n`, such that each claimed name holds what it held right after
its last entry in `K` (`NamesH.valAfter`). -/
def RegionCrashed (cl : List Claim) (n : Nat) (m' : Tree) : Prop :=
  ∃ K : Nat → Prop,
    (∀ c ∈ cl, ∀ c' ∈ cl, ∀ x e E y e' E', (x, e, E) ∈ c.2.2.ents → (y, e', E') ∈ c'.2.2.ents →
      K x → y < e.start → K y) ∧
    (∀ c ∈ cl, ∀ y e E, (y, e, E) ∈ c.2.2.ents → y < n → K y) ∧
    (∀ c ∈ cl, ∀ b, c.2.1.Mem b → m'.entry c.1 b = c.2.2.valAfter c.1 K b)

/-! ## A shared directory fd -/

/-- Where a shared directory fd's read is: not begun; begun when the log had `r0` entries, the
names of `N` returned `rs` (the reader shows a claim on `N` at each step); done. A shared fd holds
nothing of the tree. -/
inductive DirPhS where
  | idle
  | reading (N : NameSet) (r0 : Nat) (rs : List GoString)
  | done
  deriving DecidableEq

def DirPhS.enc : DirPhS → Nat × NameSet × Nat × List GoString
  | .idle => (0, .only [], 0, [])
  | .reading N r0 rs => (1, N, r0, rs)
  | .done => (2, .only [], 0, [])

instance DirPhS.countable : Pos.Countable DirPhS :=
  Pos.Countable.ofInjective (fun x => Pos.Countable.encode x.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [DirPhS.enc])

end Fs
end Perennial

end
