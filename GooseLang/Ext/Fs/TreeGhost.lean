/-
The pure part of the directory tree's ghost state (`notes/fs-v2-port-plan.md`, "The ghost state"): a
directory's entries (`Ents`, a `Dir`), the changes made to them (`LOp`), what a directory knows of
them (`DirG`: entries as of a point, and the changes since), and a directory's view of the tree's
history (`dview`): the entries of the directory of inode `j` in the tree a generation booted with,
and the change each logged operation makes to them (`lopFor`). With directories as inodes, an
operation changes the entries of the directories it names, so a view is read off the operation
alone (the one exception, a rename into `j`, reads the node the tree had at the source). Untrusted.
-/
module

public import GooseLang.Ext.Fs.Tree
public import Perennial.Std.Countable

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-! ## Entries and their changes -/

/-- A directory's entries: name to node. -/
abbrev Ents := Dir

/-- A change of a directory's entries: a name set to a node (a creation, or a file replaced), a
name removed, a rename within the directory (atomic: a crash keeps it whole or not at all). -/
inductive LOp where
  | put (b : GoString) (n : Node)
  | del (b : GoString)
  | mv (b c : GoString)

def LOp.apply : LOp → Ents → Ents
  | .put b n, m => <[b := n]> m
  | .del b, m => GMap.delete b m
  | .mv b c, m => match m !! b with
    | some n => <[c := n]> (GMap.delete b m)
    | none => m

/-- The changes `ops`, in order, replayed on `m`. -/
def lreplay (ops : List LOp) (m : Ents) : Ents := ops.foldl (fun m o => o.apply m) m

theorem lreplay_append (a b : List LOp) (m : Ents) :
    lreplay (a ++ b) m = lreplay b (lreplay a m) := by
  simp [lreplay, List.foldl_append]

theorem lreplay_snoc (a : List LOp) (o : LOp) (m : Ents) :
    lreplay (a ++ [o]) m = o.apply (lreplay a m) := by
  rw [lreplay_append]; rfl

theorem lreplay_single (o : LOp) (e : Ents) : lreplay [o] e = o.apply e := rfl

theorem replay_append (a b : List MetaOp) (m : Tree) :
    replay (a ++ b) m = replay b (replay a m) := by
  simp [replay, List.foldl_append]

theorem replay_snoc (a : List MetaOp) (o : MetaOp) (m : Tree) :
    replay (a ++ [o]) m = o.apply (replay a m) := by
  rw [replay_append]; rfl

/-! ## The entries of a directory of a tree -/

/-- The entries of the directory `j` of the tree `m` (none if `m` has no such directory). -/
def entsOf (m : Tree) (j : Ino) : Ents := (m !! j).getD ∅

theorem entsOf_lookup (m : Tree) (j : Ino) (b : GoString) : entsOf m j !! b = m.entry j b := by
  unfold entsOf Tree.entry; cases m !! j <;> rfl

theorem entsOf_upd_eq (m : Tree) (j : Ino) (f : Dir → Dir) : entsOf (m.upd j f) j = f (entsOf m j) := by
  simp [entsOf, Tree.upd]

theorem entsOf_upd_ne (m : Tree) {j j' : Ino} (f : Dir → Dir) (h : j' ≠ j) :
    entsOf (m.upd j' f) j = entsOf m j := by
  simp [entsOf, Tree.upd, h]

theorem entsOf_insert_ne (m : Tree) {j j' : Ino} (e : Dir) (h : j' ≠ j) :
    entsOf (<[j' := e]> m) j = entsOf m j := by
  simp [entsOf, h]

theorem entsOf_insert_eq (m : Tree) (j : Ino) (e : Dir) : entsOf (<[j := e]> m) j = e := by
  simp [entsOf]

/-! ## Ghost values -/

/-- What the ghost state knows of a directory: its entries as of a point known durable, and the
changes since, in order; its entries now are the changes replayed on them (`DirG.now`). A crash
leaves some prefix of the changes replayed. -/
structure DirG where
  dur : Ents
  pend : List LOp

/-- The entries now. -/
def DirG.now (g : DirG) : Ents := lreplay g.pend g.dur

/-- The entries a crash may leave. -/
def DirG.CrashTo (g : DirG) (e : Ents) : Prop :=
  ∃ i, i ≤ g.pend.length ∧ e = lreplay (g.pend.take i) g.dur

/-- `g` with the change `o` made. -/
def DirG.push (g : DirG) (o : LOp) : DirG := ⟨g.dur, g.pend ++ [o]⟩

theorem DirG.push_now (g : DirG) (o : LOp) : (g.push o).now = o.apply g.now := by
  simp [DirG.push, DirG.now, lreplay_snoc]

theorem DirG.crashTo_now (g : DirG) : g.CrashTo g.now := ⟨g.pend.length, Nat.le_refl _, by simp [DirG.now]⟩

def Node.enc : Node → Bool × Nat
  | .file i => (true, i)
  | .dir j => (false, j)

instance Node.countable : Pos.Countable Node :=
  Pos.Countable.ofInjective (fun n => Pos.Countable.encode n.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [Node.enc])

def LOp.enc : LOp → Nat × GoString × GoString × Option Node
  | .put b n => (0, b, [], some n)
  | .del b => (1, b, [], none)
  | .mv b c => (2, b, c, none)

instance LOp.countable : Pos.Countable LOp :=
  Pos.Countable.ofInjective (fun o => Pos.Countable.encode o.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [LOp.enc])

instance DirG.countable : Pos.Countable DirG :=
  Pos.Countable.ofInjective (fun g => Pos.Countable.encode (g.dur, g.pend))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1 h2; rfl)

def MetaOp.enc : MetaOp → Nat × Ino × GoString × Ino × GoString × Option Node × Option Node
  | .create j b i => (0, j, b, i, [], none, none)
  | .mkdir j b j' => (1, j, b, j', [], none, none)
  | .remove j b n => (2, j, b, 0, [], some n, none)
  | .rename j b j' b' n old => (3, j, b, j', b', some n, old)

instance MetaOp.countable : Pos.Countable MetaOp :=
  Pos.Countable.ofInjective (fun o => Pos.Countable.encode o.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [MetaOp.enc])

instance LogEntry.countable : Pos.Countable LogEntry :=
  Pos.Countable.ofInjective (fun e => Pos.Countable.encode (e.op, e.start))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1 h2; rfl)

/-! ## The difference of two directories' entries -/

/-- `b` set to its value in `e2`. -/
def setTo (e2 : Ents) (b : GoString) : LOp :=
  match e2 !! b with
  | some n => .put b n
  | none => .del b

open Classical in
/-- Changes taking `e1` to `e2`: none if they are equal, else every name of either set to its
value in `e2`. -/
def lopsDiff (e1 e2 : Ents) : List LOp :=
  if e1 = e2 then [] else ((e1.toList ++ e2.toList).map Prod.fst).map (setTo e2)

theorem lreplay_setTo (e2 : Ents) (K : List GoString) (m : Ents) (c : GoString) :
    lreplay (K.map (setTo e2)) m !! c = if c ∈ K then e2 !! c else m !! c := by
  induction K generalizing m with
  | nil => simp [lreplay]
  | cons b K ih =>
    show lreplay (K.map (setTo e2)) ((setTo e2 b).apply m) !! c = _
    rw [ih]
    by_cases hc : c ∈ K
    · simp [hc]
    · simp only [hc, ↓reduceIte, List.mem_cons, _root_.or_false]
      by_cases hbc : b = c
      · subst hbc
        simp only [↓reduceIte]
        unfold setTo
        cases h : e2 !! b with
        | none => show (GMap.delete b m) !! b = none; exact GMap.lookup_delete_eq _ _
        | some n => show (<[b := n]> m) !! b = some n; exact GMap.lookup_insert _ _ _
      · rw [if_neg (Ne.symm hbc)]
        unfold setTo
        cases e2 !! b with
        | none => exact GMap.lookup_delete_ne _ hbc
        | some n => exact GMap.lookup_insert_ne _ _ hbc

theorem lreplay_lopsDiff (e1 e2 : Ents) : lreplay (lopsDiff e1 e2) e1 = e2 := by
  unfold lopsDiff
  split
  · rename_i h; subst h; rfl
  · apply GMap.ext; intro c
    rw [lreplay_setTo]
    split
    · rfl
    · rename_i hc
      have h1 : e1 !! c = none := by
        cases h : e1 !! c with
        | none => rfl
        | some v => exact absurd (List.mem_map.2 ⟨(c, v), List.mem_append_left _ ((GMap.mem_toList _ _ _).2 h), rfl⟩) hc
      have h2 : e2 !! c = none := by
        cases h : e2 !! c with
        | none => rfl
        | some v => exact absurd (List.mem_map.2 ⟨(c, v), List.mem_append_right _ ((GMap.mem_toList _ _ _).2 h), rfl⟩) hc
      rw [h1, h2]

/-! ## A directory's view of the tree's history -/

/-- The changes an operation on the tree `m` makes to the entries of the directory `j`: one `LOp`
for an operation on `j`'s entries; for the directory `mkdir` makes, its entries' difference. -/
def lopFor (m : Tree) (j : Ino) (o : MetaOp) : List LOp :=
  match o with
  | .create j0 b i => if j0 = j then [.put b (.file i)] else []
  | .mkdir j0 b j' =>
    if j' = j then lopsDiff (entsOf m j) ∅ else if j0 = j then [.put b (.dir j')] else []
  | .remove j0 b _ => if j0 = j then [.del b] else []
  | .rename j0 b j1 b' _ _ =>
    if j0 = j ∧ j1 = j then [.mv b b']
    else if j0 = j then [.del b]
    else if j1 = j then (match m.entry j0 b with
      | some n => [.put b' n]
      | none => [])
    else []

theorem lopFor_correct (m : Tree) (j : Ino) (o : MetaOp) :
    lreplay (lopFor m j o) (entsOf m j) = entsOf (o.apply m) j := by
  cases o with
  | create j0 b i =>
    simp only [lopFor, MetaOp.apply]
    split
    · rename_i h; subst h; rw [lreplay_single, entsOf_upd_eq]; rfl
    · rename_i h; rw [entsOf_upd_ne _ _ h]; rfl
  | mkdir j0 b j' =>
    simp only [lopFor, MetaOp.apply]
    split
    · rename_i h; subst h; rw [lreplay_lopsDiff, entsOf_insert_eq]
    · rename_i h
      rw [entsOf_insert_ne _ _ h]
      split
      · rename_i h0; subst h0; rw [lreplay_single, entsOf_upd_eq]; rfl
      · rename_i h0; rw [entsOf_upd_ne _ _ h0]; rfl
  | remove j0 b n =>
    simp only [lopFor, MetaOp.apply]
    split
    · rename_i h; subst h; rw [lreplay_single, entsOf_upd_eq]; rfl
    · rename_i h; rw [entsOf_upd_ne _ _ h]; rfl
  | rename j0 b j1 b' n old =>
    simp only [lopFor, MetaOp.apply]
    split
    · rename_i h; obtain ⟨h0, h1⟩ := h; subst h1; subst h0
      rw [lreplay_single]
      show (match entsOf m j0 !! b with
        | some n => <[b' := n]> (GMap.delete b (entsOf m j0))
        | none => entsOf m j0) = _
      rw [entsOf_lookup]
      cases he : m.entry j0 b with
      | none => rfl
      | some n => simp only; rw [entsOf_upd_eq, entsOf_upd_eq]
    · rename_i h
      split
      · rename_i h0; subst h0
        have h1 : j1 ≠ j0 := fun h1 => h ⟨rfl, h1⟩
        rw [lreplay_single]
        cases he : m.entry j0 b with
        | none =>
          simp only
          show GMap.delete b (entsOf m j0) = entsOf m j0
          apply GMap.ext; intro c
          by_cases hc : b = c
          · subst hc; rw [GMap.lookup_delete_eq, entsOf_lookup, he]
          · rw [GMap.lookup_delete_ne _ hc]
        | some n =>
          simp only
          rw [entsOf_upd_ne _ _ h1, entsOf_upd_eq]; rfl
      · rename_i h0
        split
        · rename_i h1; subst h1
          cases he : m.entry j0 b with
          | none => rfl
          | some n =>
            simp only
            rw [lreplay_single, entsOf_upd_eq, entsOf_upd_ne _ _ h0]; rfl
        · rename_i h1
          cases he : m.entry j0 b with
          | none => rfl
          | some n => simp only; rw [entsOf_upd_ne _ _ h1, entsOf_upd_ne _ _ h0]; rfl

/-- The changes of `j`'s entries along the operations `H`, from the tree `m`. -/
def lopsAlong : Tree → List MetaOp → Ino → List LOp
  | _, [], _ => []
  | m, o :: os, j => lopFor m j o ++ lopsAlong (o.apply m) os j

/-- The history of the tree: the tree a generation booted with, and the entries logged since. -/
abbrev Hist := Tree × List LogEntry

/-- The operations of a history. -/
def Hist.ops (V : Hist) : List MetaOp := V.2.map (·.op)

/-- The tree now, after a history. -/
def Hist.now (V : Hist) : Tree := replay V.ops V.1

/-- The view of the directory `j` after the operations `H` from the tree `H0`. -/
def dviewOps (H0 : Tree) (H : List MetaOp) (j : Ino) : DirG := ⟨entsOf H0 j, lopsAlong H0 H j⟩

/-- The view of the directory `j` of the history `V`. -/
def dview (V : Hist) (j : Ino) : DirG := dviewOps V.1 V.ops j

theorem lreplay_lopsAlong (m : Tree) (H : List MetaOp) (j : Ino) :
    lreplay (lopsAlong m H j) (entsOf m j) = entsOf (replay H m) j := by
  induction H generalizing m with
  | nil => rfl
  | cons o os ih =>
    show lreplay (lopFor m j o ++ lopsAlong (o.apply m) os j) _ = entsOf (replay os (o.apply m)) j
    rw [lreplay_append, lopFor_correct, ih]

theorem dview_now (V : Hist) (j : Ino) : (dview V j).now = entsOf V.now j :=
  lreplay_lopsAlong V.1 V.ops j

theorem lopsAlong_take (m : Tree) (H : List MetaOp) (j : Ino) (n : Nat) :
    ∃ i, i ≤ (lopsAlong m H j).length ∧ (lopsAlong m H j).take i = lopsAlong m (H.take n) j := by
  induction H generalizing m n with
  | nil => exact ⟨0, by simp, by simp [lopsAlong]⟩
  | cons o os ih =>
    cases n with
    | zero => exact ⟨0, by simp, by simp [lopsAlong]⟩
    | succ n =>
      obtain ⟨i, hi, he⟩ := ih (o.apply m) n
      refine ⟨(lopFor m j o).length + i, ?_, ?_⟩
      · simp only [lopsAlong, List.length_append]; omega
      · simp only [lopsAlong, List.take_succ_cons]
        rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, he]

/-- **Every prefix of the history leaves the directory one of its view's crash outcomes.** -/
theorem dview_crashTo (V : Hist) (j : Ino) (n : Nat) :
    (dview V j).CrashTo (entsOf (replay (V.ops.take n) V.1) j) := by
  obtain ⟨i, hi, he⟩ := lopsAlong_take V.1 V.ops j n
  refine ⟨i, hi, ?_⟩
  show _ = lreplay ((lopsAlong V.1 V.ops j).take i) (entsOf V.1 j)
  rw [he, lreplay_lopsAlong]

theorem lopsAlong_snoc (m : Tree) (H : List MetaOp) (o : MetaOp) (j : Ino) :
    lopsAlong m (H ++ [o]) j = lopsAlong m H j ++ lopFor (replay H m) j o := by
  induction H generalizing m with
  | nil => simp [lopsAlong, replay]
  | cons o' os ih =>
    show lopFor m j o' ++ lopsAlong (o'.apply m) (os ++ [o]) j = _
    rw [ih]; simp [lopsAlong, replay, List.foldl]

/-- The history with one more entry. -/
def Hist.push (V : Hist) (e : LogEntry) : Hist := (V.1, V.2 ++ [e])

theorem Hist.push_ops (V : Hist) (e : LogEntry) : (V.push e).ops = V.ops ++ [e.op] := by
  simp [Hist.push, Hist.ops]

theorem Hist.push_now (V : Hist) (e : LogEntry) : (V.push e).now = e.op.apply V.now := by
  simp only [Hist.now, Hist.push_ops, replay_snoc]; rfl

theorem dview_push (V : Hist) (e : LogEntry) (j : Ino) :
    dview (V.push e) j = ⟨(dview V j).dur, (dview V j).pend ++ lopFor V.now j e.op⟩ := by
  unfold dview dviewOps; rw [Hist.push_ops, lopsAlong_snoc]; rfl

/-- A file created, removed or renamed within `j`, or a directory made in `j`: the view pushes its
one change. -/
theorem dview_create (V : Hist) (j : Ino) (b : GoString) (i s : Nat) :
    dview (V.push ⟨.create j b i, s⟩) j = (dview V j).push (.put b (.file i)) := by
  rw [dview_push]; simp [lopFor, DirG.push]

theorem dview_mkdir (V : Hist) (j : Ino) (b : GoString) (j' s : Nat) (hj : j' ≠ j) :
    dview (V.push ⟨.mkdir j b j', s⟩) j = (dview V j).push (.put b (.dir j')) := by
  rw [dview_push]; simp [lopFor, DirG.push, hj]

theorem dview_remove (V : Hist) (j : Ino) (b : GoString) (n : Node) (s : Nat) :
    dview (V.push ⟨.remove j b n, s⟩) j = (dview V j).push (.del b) := by
  rw [dview_push]; simp [lopFor, DirG.push]

theorem dview_rename (V : Hist) (j : Ino) (b b' : GoString) (n : Node) (old : Option Node) (s : Nat) :
    dview (V.push ⟨.rename j b j b' n old, s⟩) j = (dview V j).push (.mv b b') := by
  rw [dview_push]; simp [lopFor, DirG.push]

/-- An operation that does not name `j` leaves its view. -/
theorem dview_other (V : Hist) (j : Ino) (e : LogEntry) (h : lopFor V.now j e.op = []) :
    dview (V.push e) j = dview V j := by
  rw [dview_push, h, List.append_nil]

/-- No operation: the view of the empty history. -/
theorem dview_nil (m : Tree) (j : Ino) : dview (m, []) j = ⟨entsOf m j, []⟩ := rfl

end Fs
end Perennial

end
