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

/-- The roots of the tree: each a path and its directory's inode. -/
abbrev Roots := List (GoString × Ino)

/-! ## What the claims know, as a function of the history, and the claims a generation starts with

(Used by the tree's start resources, `treeStart`, in `Ghost.lean`.) -/

/-- What a claim on no name knows. -/
def NamesH.empty : NamesH := ⟨∅, [], ∅⟩

open Classical in
/-- The claim on the names `N` of the directory `j`, as the history `V` has them: their entries at
boot, each entry writing one of them (with their entries right after), their entries now. -/
def namesOf (V : Hist) (j : Ino) (N : NameSet) : NamesH where
  boot := restrictN N (entsOf V.1 j)
  ents := (List.range V.2.length).filterMap (fun x => match V.2[x]? with
    | some e => if ∃ b, N.Mem b ∧ e.op.Writes j b then
        some (x, e, restrictN N (entsOf (prefTree V.1 V.2 (x + 1)) j)) else none
    | none => none)
  cur := restrictN N (entsOf V.now j)

/-- The claims' coherence with the shared history `V`: each claim's history is the history's; the
claims of a directory are disjoint; every name of every directory of the tree is claimed; every
claimed directory is one of the tree (so a fresh directory's key is free); and of the log alone, every
entry's call began no later than it took effect (`Starts`, the state's `TreeCohS.starts`: a client
reasons about crashes of the claims it holds with it, `osClaims_log`). -/
structure NamesCoh (V : Hist) (Γn : GMap (Ino × NameSet) NamesH) : Prop where
  hist : ∀ j N h, Γn !! (j, N) = some h → h = namesOf V j N
  disj : ∀ j N N' h h' b, Γn !! (j, N) = some h → Γn !! (j, N') = some h' → N ≠ N' →
    N.Mem b → ¬ N'.Mem b
  cover : ∀ j b, j ∈ V.now → ∃ N h, Γn !! (j, N) = some h ∧ N.Mem b
  dirs : ∀ j N h, Γn !! (j, N) = some h → j ∈ V.now
  starts : Starts V.2

/-- The log's entries, as a map. -/
def logMap (log : List LogEntry) : GMap Nat LogEntry :=
  (List.range log.length).foldl (fun m x => match log[x]? with
    | some e => <[x := e]> m
    | none => m) ∅


theorem logMap_nil : logMap ([] : List LogEntry) = ∅ := rfl

/-- The keys of the call permission on the roots `R`: each root, and `[]` (the paths under no
root). -/
def permMap (R : Roots) : GMap GoString Unit :=
  GMap.ofList (([], ()) :: R.map (fun rj => (rj.1, ())))

theorem permMap_lookup (R : Roots) (r : GoString) (h : r = [] ∨ ∃ j, (r, j) ∈ R) :
    permMap R !! r = some () := by
  unfold permMap
  rcases h with rfl | ⟨j, hj⟩
  · show GMap.lookup (GMap.insert _ _ _) _ = _; rw [GMap.lookup_insert]
  · show GMap.lookup (GMap.insert _ _ _) _ = _
    by_cases h0 : ([] : GoString) = r
    · subst h0; rw [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ h0]
      clear h0
      induction R with
      | nil => simp at hj
      | cons rj R ih =>
        show GMap.lookup (GMap.insert _ _ _) _ = _
        by_cases h1 : rj.1 = r
        · rw [h1, GMap.lookup_insert]
        · rw [GMap.lookup_insert_ne _ _ h1]
          rcases List.mem_cons.1 hj with h2 | h2
          · subst h2; exact absurd rfl h1
          · exact ih h2

/-- The log as a map has the log's entries. -/
theorem logMap_lookup (log : List LogEntry) (x : Nat) : logMap log !! x = log[x]? := by
  have key : ∀ n, ((List.range n).foldl (fun m x => match log[x]? with
      | some e => <[x := e]> m
      | none => m) (∅ : GMap Nat LogEntry)) !! x = if x < n then log[x]? else none := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases hn : log[n]? with
      | none =>
        simp only []
        rw [ih]
        by_cases hx : x < n
        · simp [hx, Nat.lt_succ_of_lt hx]
        · by_cases hxn : x = n
          · subst hxn; simp [hn]
          · have : ¬ x < n + 1 := by omega
            simp [hx, this]
      | some e =>
        simp only []
        by_cases hxn : n = x
        · subst hxn; rw [GMap.lookup_insert]; simp [hn]
        · rw [GMap.lookup_insert_ne _ _ hxn, ih]
          by_cases hx : x < n
          · simp [hx, Nat.lt_succ_of_lt hx]
          · have : ¬ x < n + 1 := by omega
            simp [hx, this]
  unfold logMap
  refine (key log.length).trans ?_
  by_cases hx : x < log.length
  · simp [hx]
  · simp [hx, List.getElem?_eq_none (by omega : log.length ≤ x)]

/-- The claims a switch allocates: one on all the names of each directory of `js`. -/
def claimsInit (V : Hist) : List Ino → GMap (Ino × NameSet) NamesH
  | [] => ∅
  | j :: js => <[(j, .except []) := namesOf V j (.except [])]> (claimsInit V js)

theorem claimsInit_lookup (V : Hist) (js : List Ino) (k : Ino × NameSet) :
    claimsInit V js !! k = if k.2 = .except [] ∧ k.1 ∈ js then some (namesOf V k.1 k.2) else none := by
  induction js with
  | nil => simp [claimsInit]
  | cons j js ih =>
    unfold claimsInit
    by_cases hk : (j, NameSet.except []) = k
    · subst hk; rw [GMap.lookup_insert]; simp
    · rw [GMap.lookup_insert_ne _ _ hk, ih]
      obtain ⟨k1, k2⟩ := k
      by_cases h2 : k2 = .except []
      · subst h2
        have : k1 ≠ j := fun h => hk (by rw [h])
        simp [this]
      · simp [h2]

/-- The claims a switch allocates are coherent with the history. -/
theorem namesCoh_init (V : Hist) (hs : Starts V.2) :
    NamesCoh V (claimsInit V ((GMap.toList V.now).map (·.1))) := by
  refine ⟨fun j N h hl => ?_, fun j N N' h h' b hl hl' hne _ => ?_, fun j b hj => ?_,
    fun j N h hl => ?_, hs⟩
  · rw [claimsInit_lookup] at hl
    split at hl
    · cases hl; rfl
    · cases hl
  · rw [claimsInit_lookup] at hl hl'
    split at hl
    · split at hl'
      · rename_i h1 h2; exact absurd (h1.1.trans h2.1.symm) hne
      · cases hl'
    · cases hl
  · refine ⟨.except [], namesOf V j (.except []), ?_, by simp [NameSet.Mem]⟩
    rw [claimsInit_lookup]
    have hm : j ∈ (GMap.toList V.now).map (·.1) := by
      rw [GMap.mem_iff] at hj
      cases hv : V.now !! j with
      | none => rw [hv] at hj; exact absurd hj (by simp)
      | some v => exact List.mem_map.2 ⟨(j, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
    simp [hm]
  · rw [claimsInit_lookup] at hl
    split at hl
    · rename_i hk
      obtain ⟨⟨j1, v⟩, hv, hj1⟩ := List.mem_map.1 hk.2
      simp only at hj1
      subst hj1
      rw [GMap.mem_iff, (GMap.mem_toList _ _ _).1 hv]; rfl
    · cases hl

/-- The directories of the tree, each once. -/
abbrev dirsOf (V : Hist) : List Ino := (GMap.toList V.now).map (·.1)

end Fs
end Perennial

end
