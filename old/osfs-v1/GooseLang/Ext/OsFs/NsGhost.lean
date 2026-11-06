/-
The pure part of the namespace's ghost state (`notes/walfs-ext-plan.md`, "The program logic of the
namespace"): a directory's entries, by last component (`Ents`), the changes a client makes to them
(`LOp`), and the entries of a directory of a namespace (`entsOf`), with the laws that relate the
namespace's operations (`NsOp`) to them. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.Impl
public import Perennial.Std.Countable

@[expose] public section

noncomputable section

namespace Perennial

/-! ## Entries and their changes -/

/-- A directory's entries: last component to node. -/
abbrev Ents := GMap GoString OsNode

/-- A change of a directory's entries: a name set to a node (a creation, or a file replaced), a
name removed, a rename within the directory (atomic: a crash keeps it whole or not at all). -/
inductive LOp where
  | put (b : GoString) (n : OsNode)
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

theorem nsReplay_append (a b : List NsOp) (m : NsMap) :
    nsReplay (a ++ b) m = nsReplay b (nsReplay a m) := by
  simp [nsReplay, List.foldl_append]

theorem nsReplay_snoc (a : List NsOp) (o : NsOp) (m : NsMap) :
    nsReplay (a ++ [o]) m = o.apply (nsReplay a m) := by
  rw [nsReplay_append]; rfl

/-- A prefix of the log after a commit of its first `k` operations is a longer prefix of the log
before it: a commit keeps every crash outcome a crash had before it (the program logic's
coherence of a directory's entries survives anyone's commit). -/
theorem nsReplay_commit (log : List NsOp) (dur : NsMap) (k n : Nat) :
    nsReplay ((log.drop k).take n) (nsReplay (log.take k) dur) = nsReplay (log.take (k + n)) dur := by
  rw [← nsReplay_append, List.take_add]

/-! ## The entries of a directory of a namespace -/

/-- The entries of the directory `d` of the namespace `m`: the nodes of `d/b`, `b` a valid name. -/
def entsOf (m : NsMap) (d : GoString) : Ents :=
  ⟨fun b => if NameOk b then m !! (d ++ slashB :: b) else none, by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l.map (fun k => k.drop (d.length + 1)), fun b hb => ?_⟩
    by_cases hn : NameOk b
    · simp only [hn, ↓reduceIte] at hb
      exact List.mem_map.2 ⟨_, hl _ hb, by simp⟩
    · simp [hn] at hb⟩

theorem entsOf_lookup (m : NsMap) (d b : GoString) :
    entsOf m d !! b = if NameOk b then m !! (d ++ slashB :: b) else none := rfl

/-- The last component and the directory of `d/b`, for a valid name `b`. -/
theorem baseOf_child (d b : GoString) (hb : slashB ∉ b) : baseOf (d ++ slashB :: b) = b := by
  unfold baseOf
  have h1 : (d ++ slashB :: b).reverse = b.reverse ++ slashB :: d.reverse := by simp
  rw [h1]
  have h2 : ∀ x ∈ b.reverse, (fun c => decide (c ≠ slashB)) x = true := by
    intro x hx; simp only [List.mem_reverse] at hx
    simp only [ne_eq, decide_eq_true_eq]; intro h; subst h; exact hb hx
  rw [List.takeWhile_append_of_pos h2]
  simp [slashB]

theorem parentOf_child (d b : GoString) (hb : slashB ∉ b) :
    parentOf (d ++ slashB :: b) = some d := by
  unfold parentOf
  simp only [baseOf_child d b hb]
  have : b.length < (d ++ slashB :: b).length := by simp; omega
  simp only [this, ↓reduceIte, Option.some.injEq]
  have hl : (d ++ slashB :: b).length - b.length - 1 = d.length := by simp; omega
  rw [hl]; simp

/-- Setting `d/b` sets `b` in `d`'s entries. -/
theorem entsOf_insert_child (m : NsMap) (d b : GoString) (n : OsNode) (hb : NameOk b) :
    entsOf (<[d ++ slashB :: b := n]> m) d = <[b := n]> (entsOf m d) := by
  apply GMap.ext; intro c
  show entsOf _ d !! c = (<[b := n]> (entsOf m d)) !! c
  rw [entsOf_lookup]
  by_cases hbc : b = c
  · subst hbc; rw [GMap.lookup_insert]; simp [hb, GMap.lookup_insert]
  · rw [GMap.lookup_insert_ne _ _ hbc, entsOf_lookup]
    split
    · have : d ++ slashB :: b ≠ d ++ slashB :: c := by
        intro h; exact hbc (List.cons.inj (List.append_cancel_left h)).2
      rw [GMap.lookup_insert_ne _ _ this]
    · rfl

/-- Removing `d/b` removes `b` from `d`'s entries. -/
theorem entsOf_delete_child (m : NsMap) (d b : GoString) :
    entsOf (GMap.delete (d ++ slashB :: b) m) d = GMap.delete b (entsOf m d) := by
  apply GMap.ext; intro c
  show entsOf _ d !! c = (GMap.delete b (entsOf m d)) !! c
  rw [entsOf_lookup]
  by_cases hbc : b = c
  · subst hbc; rw [GMap.lookup_delete]; split <;> simp [GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ hbc, entsOf_lookup]
    split
    · have : d ++ slashB :: b ≠ d ++ slashB :: c := by
        intro h; exact hbc (List.cons.inj (List.append_cancel_left h)).2
      rw [GMap.lookup_delete_ne _ this]
    · rfl

/-- Setting or removing a path not in `d` leaves `d`'s entries. -/
theorem entsOf_insert_other (m : NsMap) (d p : GoString) (n : OsNode)
    (hp : parentOf p ≠ some d) : entsOf (<[p := n]> m) d = entsOf m d := by
  apply GMap.ext; intro c
  show entsOf _ d !! c = entsOf m d !! c
  rw [entsOf_lookup, entsOf_lookup]
  split
  · rename_i hc
    have : p ≠ d ++ slashB :: c := by
      intro h; subst h; exact hp (parentOf_child d c hc.2.2.2.1)
    rw [GMap.lookup_insert_ne _ _ this]
  · rfl

theorem entsOf_delete_other (m : NsMap) (d p : GoString) (hp : parentOf p ≠ some d) :
    entsOf (GMap.delete p m) d = entsOf m d := by
  apply GMap.ext; intro c
  show entsOf _ d !! c = entsOf m d !! c
  rw [entsOf_lookup, entsOf_lookup]
  split
  · rename_i hc
    have : p ≠ d ++ slashB :: c := by
      intro h; subst h; exact hp (parentOf_child d c hc.2.2.2.1)
    rw [GMap.lookup_delete_ne _ this]
  · rfl

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
def DirG.CrashTo (g : DirG) (e : Ents) : Prop := ∃ i, i ≤ g.pend.length ∧ e = lreplay (g.pend.take i) g.dur

def OsNode.enc : OsNode → Option GoString
  | .file k => some k
  | .dir => none

instance OsNode.countable : Pos.Countable OsNode :=
  Pos.Countable.ofInjective (fun n => Pos.Countable.encode n.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [OsNode.enc])

def LOp.enc : LOp → Nat × GoString × GoString × Option OsNode
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

/-! ## A directory's view from the namespace's history (`NsView.lean` has its laws) -/

def NsOp.enc : NsOp → Nat × GoString × GoString
  | .create p k => (0, p, k)
  | .mkdir p => (1, p, [])
  | .remove p => (2, p, [])
  | .rename s t => (3, s, t)

instance NsOp.countable : Pos.Countable NsOp :=
  Pos.Countable.ofInjective (fun o => Pos.Countable.encode o.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [NsOp.enc])


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


/-- Whether `s` holds a file in `m`. -/
def isFileAt (m : NsMap) (s : GoString) : Bool :=
  match m !! s with
  | some (.file _) => true
  | _ => false

/-- The changes an operation on the namespace `m` makes to the entries of `d`: the one `LOp` of a
file operation of `d`'s entries; otherwise their difference. -/
def lopFor (m : NsMap) (d : GoString) (o : NsOp) : List LOp :=
  match o with
  | .create p k =>
    if p = (d ++ slashB :: baseOf p) ∧ NameOk (baseOf p) then [.put (baseOf p) (.file k)]
    else lopsDiff (entsOf m d) (entsOf (o.apply m) d)
  | .mkdir p =>
    if p = (d ++ slashB :: baseOf p) ∧ NameOk (baseOf p) then [.put (baseOf p) .dir]
    else lopsDiff (entsOf m d) (entsOf (o.apply m) d)
  | .remove p =>
    if p = (d ++ slashB :: baseOf p) ∧ NameOk (baseOf p) then [.del (baseOf p)]
    else lopsDiff (entsOf m d) (entsOf (o.apply m) d)
  | .rename s t =>
    if s = (d ++ slashB :: baseOf s) ∧ t = (d ++ slashB :: baseOf t) ∧ NameOk (baseOf s) ∧ NameOk (baseOf t) ∧
        baseOf s ≠ baseOf t ∧ isFileAt m s = true then [.mv (baseOf s) (baseOf t)]
    else lopsDiff (entsOf m d) (entsOf (o.apply m) d)


/-- The changes of `d`'s entries along the operations `H`, from the namespace `m`. -/
def lopsAlong : NsMap → List NsOp → GoString → List LOp
  | _, [], _ => []
  | m, o :: os, d => lopFor m d o ++ lopsAlong (o.apply m) os d

/-- The view of the directory `d` after the operations `H` from the namespace `H0`. -/
def dview (H0 : NsMap) (H : List NsOp) (d : GoString) : DirG := ⟨entsOf H0 d, lopsAlong H0 H d⟩


/-- `d` is a directory in every prefix of the history `V`. -/
def AllDir (V : NsMap × List NsOp) (d : GoString) : Prop :=
  ∀ n, nsReplay (V.2.take n) V.1 !! d = some .dir

end Perennial

end
