/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: canonical placement of a pending write (`SharedModel`'s full mode)

`SharedModel` (`examples/k8s/dist/storecopy/export.go`) checks the store's history on the shared
cluster: the driver's `Model` with foreign revisions. Before each operation, its full mode lets each
pending write take effect at one of `landings(revs, c, w, b, true, in, out)`: the next revision, and,
above it, every revision the history shows for the write's key, the answer's own revision for that
key, and every anchor at or above the configuration's revision and the one after it. The cluster may
have put the write at any revision `R` above the configuration's. Completeness rests on one fact,
proved here over the revision numbers alone: `R` can be replaced by `canonL anchors rv R` (`R` itself
if the history names it, else one above the greatest of the configuration's revision and the anchors
below `R`), which is one of the landings (`canonL_mem`), is no later (`canonL_le`), and which no
revision the history names, nor one after it, tells from `R` (`canonL_cut`): every past read, every
watch range's bound and every resource version the answers compare against is such a revision. The
store-level argument (the renaming of the moved revisions, the target, the watch-list gap) is
`notes/k8s-dist-k4.md`.
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

/-- **`landings` in the full mode**, as a list of revisions (its order does not matter): the next
revision `rv + 1`, and those of the key's revisions `keyRevs` (`revs.byKey[w.Key]`), of the answer's
own revision for the key `own` (none or one) and of the anchors at or above `rv` and the ones after
them that are above `rv + 1`. -/
def landingsFull (anchors keyRevs own : List Nat) (rv : Nat) : List Nat :=
  (rv + 1) :: ((keyRevs ++ own ++ (anchors.filter (fun a => rv ≤ a)).flatMap (fun a => [a, a + 1])).filter
    (fun r => rv + 1 < r))

/-- The greatest anchor below `R` (0 if none). -/
def anchorBelow (anchors : List Nat) (R : Nat) : Nat := (anchors.filter (· < R)).foldr max 0

/-- **The canonical landing** of a write the cluster put at `R`, from a configuration at `rv`: `R`
if the history names it, else just above the configuration's revision and every anchor below `R`. -/
def canonL (anchors : List Nat) (rv R : Nat) : Nat :=
  if R ∈ anchors then R else max rv (anchorBelow anchors R) + 1

theorem foldr_max_ge (l : List Nat) (q : Nat) (h : q ∈ l) : q ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem foldr_max_mem (l : List Nat) : l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
  induction l with
  | nil => left; rfl
  | cons x l ih =>
    simp only [List.foldr_cons]
    rcases Nat.le_total x (l.foldr max 0) with hle | hle
    · rw [Nat.max_eq_right hle]
      rcases ih with h | h
      · left; exact h
      · right; exact List.mem_cons_of_mem _ h
    · rw [Nat.max_eq_left hle]; right; exact List.mem_cons_self

theorem foldr_max_lt (l : List Nat) (R : Nat) (hR : 0 < R) (h : ∀ q ∈ l, q < R) :
    l.foldr max 0 < R := by
  induction l with
  | nil => exact hR
  | cons x l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_lt.mpr ⟨h x List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- Every anchor below `R` is at most `anchorBelow`. -/
theorem anchorBelow_ge (anchors : List Nat) (R q : Nat) (hq : q ∈ anchors) (hlt : q < R) :
    q ≤ anchorBelow anchors R :=
  foldr_max_ge _ q (List.mem_filter.mpr ⟨hq, by simpa using hlt⟩)

/-- `anchorBelow` is below `R` (for `R > 0`). -/
theorem anchorBelow_lt (anchors : List Nat) (R : Nat) (hR : 0 < R) : anchorBelow anchors R < R :=
  foldr_max_lt _ R hR fun q hq => by simpa using (List.mem_filter.mp hq).2

/-- `anchorBelow` is 0 or an anchor. -/
theorem anchorBelow_mem (anchors : List Nat) (R : Nat) :
    anchorBelow anchors R = 0 ∨ anchorBelow anchors R ∈ anchors := by
  rcases foldr_max_mem (anchors.filter (· < R)) with h | h
  · left; exact h
  · right; exact (List.mem_filter.mp h).1

/-- The canonical landing is above the configuration's revision and no later than `R`. -/
theorem canonL_le (anchors : List Nat) (rv R : Nat) (h : rv < R) :
    rv < canonL anchors rv R ∧ canonL anchors rv R ≤ R := by
  unfold canonL
  split
  · exact ⟨h, Nat.le_refl _⟩
  · have := anchorBelow_lt anchors R (by omega)
    omega

/-- **The canonical landing is one of the full mode's landings.** -/
theorem canonL_mem (anchors keyRevs own : List Nat) (rv R : Nat) (h : rv < R) :
    canonL anchors rv R ∈ landingsFull anchors keyRevs own rv := by
  unfold canonL landingsFull
  split
  · next hR =>
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt h) with hlt | heq
    · refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨?_, by simpa using hlt⟩)
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨R, ?_, by simp⟩)
      exact List.mem_filter.mpr ⟨hR, by simpa using Nat.le_of_lt h⟩
    · rw [← heq]; exact List.mem_cons_self
  · rcases Nat.le_total (anchorBelow anchors R) rv with hle | hle
    · rw [Nat.max_eq_left hle]; exact List.mem_cons_self
    · rw [Nat.max_eq_right hle]
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have hb : anchorBelow anchors R ∈ anchors := by
          rcases anchorBelow_mem anchors R with h0 | h0
          · omega
          · exact h0
        refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨?_, by simpa using hlt⟩)
        refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨anchorBelow anchors R, ?_, by simp⟩)
        exact List.mem_filter.mpr ⟨hb, by simpa using hle⟩
      · rw [← heq]; exact List.mem_cons_self

/-- No anchor lies in `[canonL, R)`: moving the write from `R` down to `canonL` passes no revision
the history names. -/
theorem canonL_gap (anchors : List Nat) (rv R q : Nat) (hq : q ∈ anchors) (hlt : q < R) :
    q < canonL anchors rv R := by
  unfold canonL
  split
  · exact hlt
  · have := anchorBelow_ge anchors R q hq hlt
    omega

/-- **No named revision tells `canonL` from `R`**: for an anchor `v`, or one after an anchor, `v ≤
canonL ↔ v ≤ R`. Every revision an answer compares a store's revisions against is one: a past read's
revision, a watch range's bounds (an event's revision and the one after it, a bookmark's and the one
after it, a request's and the one after it), a minimum resource version. -/
theorem canonL_cut (anchors : List Nat) (rv R v : Nat) (h : rv < R)
    (hv : v ∈ anchors ∨ ∃ a ∈ anchors, v = a + 1) :
    v ≤ canonL anchors rv R ↔ v ≤ R := by
  have hle := (canonL_le anchors rv R h).2
  refine ⟨fun h1 => Nat.le_trans h1 hle, fun h1 => ?_⟩
  rcases hv with hv | ⟨a, ha, rfl⟩
  · rcases Nat.lt_or_eq_of_le h1 with hlt | heq
    · exact Nat.le_of_lt (canonL_gap anchors rv R v hv hlt)
    · subst heq; unfold canonL; simp [hv]
  · exact Nat.succ_le_of_lt (canonL_gap anchors rv R a ha (by omega))

/-- **A settle phase**: the writes the cluster applied before an operation, at the increasing
revisions `Rs`, from a configuration at `rv`, are put at `canonL`'s, each from the one before. -/
def canonAll (anchors : List Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | rv, R :: Rs => canonL anchors rv R :: canonAll anchors (canonL anchors rv R) Rs

/-- A settle phase's canonical landings are each a landing of the configuration before it, each
no later than the cluster's, and indistinguishable from it by any named revision; the search's
configuration stays at or below the cluster's. -/
theorem canonAll_ok (A : List Nat) :
    ∀ (Rs : List Nat) (rv rvc : Nat), rv ≤ rvc → Rs.Pairwise (· < ·) → (∀ R ∈ Rs, rvc < R) →
      (canonAll A rv Rs).length = Rs.length ∧
      ∀ p ∈ (canonAll A rv Rs).zip Rs,
        p.1 ≤ p.2 ∧ ∀ v, (v ∈ A ∨ ∃ a ∈ A, v = a + 1) → (v ≤ p.1 ↔ v ≤ p.2)
  | [], _, _, _, _, _ => ⟨rfl, fun p hp => by simp [canonAll] at hp⟩
  | R :: Rs, rv, rvc, hle, hs, hR => by
    have hR0 : rvc < R := hR R List.mem_cons_self
    have hlt : rv < R := Nat.lt_of_le_of_lt hle hR0
    have hs' := List.pairwise_cons.mp hs
    have ih := canonAll_ok A Rs (canonL A rv R) R (canonL_le A rv R hlt).2 hs'.2
      (fun R' hR' => hs'.1 R' hR')
    simp only [canonAll, List.length_cons, List.zip_cons_cons, List.mem_cons]
    refine ⟨by rw [ih.1], fun p hp => ?_⟩
    rcases hp with rfl | hp
    · exact ⟨(canonL_le A rv R hlt).2, fun v hv => canonL_cut A rv R v hlt hv⟩
    · exact ih.2 p hp

end k8s_dist
end EtcdGrove
end Perennial
