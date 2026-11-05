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

end Perennial

end
