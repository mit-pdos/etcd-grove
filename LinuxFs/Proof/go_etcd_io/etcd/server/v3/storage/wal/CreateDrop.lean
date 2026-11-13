/- Lean-first (no Rocq counterpart).

# Region crashes across `Create`'s claim changes, pure part (W4, `notes/wal-fsext-plan.md`, "W4
implementation log", eighth session)

The invariant's pure facts quantify over `RegionCrashed cl n m'` (the crashed trees its claims `cl`
allow). `Create` changes `cl` three ways:

* **adding names** (the minting merges the program's claim on `nm.tmp` into the creating claim; an
  error before the rename merges `nm.tmp` back into the area claim): every crash of the new claims is
  one of the old (`regionCrashedK_cover`: each old entry is a new claim's, each old name a new claim's
  with the same `valAfter`), so the facts carry over unchanged;
* **splitting or merging** a claim (the area claim into the creating claim and the rest; the merge
  back after the commit): the same lemma, with `valAfter_restrict` (a claim's restriction to some of
  its names agrees with it there);
* **dropping** a one-name claim (the program takes the invariant's half of `nm.tmp`):
  `regionCrashedK_drop1`, a crash of the remaining claims is, with that name reset (`treeSetE`), a
  crash of all of them. Its kept set extends the given one (`dropK`), which needs the claims' entries
  to be one log's and that log's `Starts`; the shared invariant does not yet provide them (the
  eighth session's finding).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCommit

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- `valAfter` depends on the kept set only through the claim's own entries. -/
theorem valAfter_congrK (h : NamesH) (j : Ino) (K K' : Nat → Prop) (b : GoString)
    (hK : ∀ xe ∈ h.ents, (K xe.1 ↔ K' xe.1)) : h.valAfter j K b = h.valAfter j K' b := by
  classical
  unfold NamesH.valAfter
  have e : h.ents.filter (fun xe => decide (K xe.1 ∧ xe.2.1.op.Writes j b)) =
      h.ents.filter (fun xe => decide (K' xe.1 ∧ xe.2.1.op.Writes j b)) :=
    List.filter_congr (fun xe hxe => by simp only [hK xe hxe])
  rw [e]

/-- **A claim restricted to names `M` agrees with it on them.** -/
theorem valAfter_restrict (h : NamesH) (j : Ino) (M : NameSet) (K : Nat → Prop) (b : GoString)
    (hb : M.Mem b) : (h.restrict j M).valAfter j K b = h.valAfter j K b := by
  classical
  unfold NamesH.valAfter NamesH.restrict
  simp only
  rw [List.filter_map, List.filter_filter]
  have e : ((fun xe : Nat × LogEntry × Ents => decide (K xe.1 ∧ xe.2.1.op.Writes j b)) ∘
      (fun xe : Nat × LogEntry × Ents => (xe.1, xe.2.1, restrictN M xe.2.2))) =
      (fun xe : Nat × LogEntry × Ents => decide (K xe.1 ∧ xe.2.1.op.Writes j b)) := rfl
  rw [e]
  have e2 : (h.ents.filter (fun xe : Nat × LogEntry × Ents => decide (K xe.1 ∧ xe.2.1.op.Writes j b) &&
      decide (∃ b', M.Mem b' ∧ xe.2.1.op.Writes j b'))) =
      h.ents.filter (fun xe : Nat × LogEntry × Ents => decide (K xe.1 ∧ xe.2.1.op.Writes j b)) := by
    refine List.filter_congr (fun xe _ => ?_)
    by_cases hw : K xe.1 ∧ xe.2.1.op.Writes j b
    · simp only [hw, decide_true, Bool.true_and]
      exact decide_eq_true ⟨b, hb, hw.2⟩
    · simp only [hw, decide_false, Bool.false_and]
  rw [e2, List.getLast?_map]
  cases (h.ents.filter (fun xe : Nat × LogEntry × Ents => decide (K xe.1 ∧ xe.2.1.op.Writes j b))).getLast? with
  | none => exact restrictN_lookup M _ b hb
  | some xe => exact restrictN_lookup M _ b hb

/-- An entry of a claim writing one of the names `M` is, with the same index and log entry, its
restriction's. -/
theorem mem_restrict_ents {h : NamesH} {j : Ino} {M : NameSet} {x : Nat} {e : LogEntry} {E : Ents}
    (hx : (x, e, E) ∈ h.ents) {b : GoString} (hb : M.Mem b) (hw : e.op.Writes j b) :
    (x, e, restrictN M E) ∈ (h.restrict j M).ents := by
  classical
  unfold NamesH.restrict
  simp only
  refine List.mem_map.2 ⟨(x, e, E), List.mem_filter.2 ⟨hx, ?_⟩, rfl⟩
  simp only [decide_eq_true_eq]
  exact ⟨b, hb, hw⟩

/-- An entry of a claim's restriction is, with the same index and log entry, the claim's. -/
theorem restrict_ents_mem {h : NamesH} {j : Ino} {M : NameSet} {x : Nat} {e : LogEntry} {E : Ents}
    (hx : (x, e, E) ∈ (h.restrict j M).ents) : ∃ E', (x, e, E') ∈ h.ents := by
  classical
  unfold NamesH.restrict at hx
  simp only at hx
  obtain ⟨xe, hxe, he⟩ := List.mem_map.1 hx
  obtain ⟨hxe, -⟩ := List.mem_filter.1 hxe
  rcases xe with ⟨x', e', E'⟩
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  exact ⟨E', hxe⟩

/-- **A crash of claims covering others is one of theirs**: each entry of the claims `cl` is (index
and log entry) one of `cl'`'s, and each name of a claim of `cl` is one of a claim of `cl'` on the
same directory, agreeing on it after any crash. -/
theorem regionCrashedK_cover {cl cl' : List Claim} {n : Nat} {m' : Tree} {K : Nat → Prop}
    (hents : ∀ c ∈ cl, ∀ x e E, (x, e, E) ∈ c.2.2.ents → ∃ c' ∈ cl', ∃ E', (x, e, E') ∈ c'.2.2.ents)
    (hval : ∀ c ∈ cl, ∀ b, c.2.1.Mem b → ∃ c' ∈ cl', c'.1 = c.1 ∧ c'.2.1.Mem b ∧
      ∀ K' : Nat → Prop, c'.2.2.valAfter c'.1 K' b = c.2.2.valAfter c.1 K' b)
    (hK : RegionCrashedK cl' n m' K) : RegionCrashedK cl n m' K := by
  refine ⟨fun c1 hc1 c2 hc2 x e E y e' E' hx hy hKx hlt => ?_, fun c1 hc1 y e E hy hlt => ?_,
    fun c1 hc1 b hb => ?_⟩
  · obtain ⟨d1, hd1, F1, hx'⟩ := hents c1 hc1 x e E hx
    obtain ⟨d2, hd2, F2, hy'⟩ := hents c2 hc2 y e' E' hy
    exact hK.1 d1 hd1 d2 hd2 x e F1 y e' F2 hx' hy' hKx hlt
  · obtain ⟨d1, hd1, F1, hy'⟩ := hents c1 hc1 y e E hy
    exact hK.2.1 d1 hd1 y e F1 hy' hlt
  · obtain ⟨d, hd, hdj, hdb, hdv⟩ := hval c1 hc1 b hb
    rw [← hdv K, ← hK.2.2 d hd b hdb, hdj]

/-- An entry of a claim's restriction to `M` writes a name of `M`. -/
theorem restrict_ents_writes {h : NamesH} {j : Ino} {M : NameSet} {x : Nat} {e : LogEntry} {E : Ents}
    (hx : (x, e, E) ∈ (h.restrict j M).ents) : ∃ b, M.Mem b ∧ e.op.Writes j b := by
  classical
  unfold NamesH.restrict at hx
  simp only at hx
  obtain ⟨xe, hxe, he⟩ := List.mem_map.1 hx
  obtain ⟨-, hw⟩ := List.mem_filter.1 hxe
  rcases xe with ⟨x', e', E'⟩
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  simpa using hw

/-! ## The minting's claims -/

/-- The claims after the minting: the area claim `(jr, N, h)` (holding `nm`) replaced by its part
off `nm`, and the creating claim on `[nm, tmp]` appended (its history `hC` agreeing with the area
claim's on `nm`: `osNames_merge`'s). -/
def mintClaims (cl : List Claim) (jr : Ino) (N : NameSet) (h : NamesH) (nm tmp : GoString)
    (hC : NamesH) : List Claim :=
  replClaim (jr, N, h) (jr, N.diff [nm], h.restrict jr (N.diff [nm])) cl ++
    [(jr, .only [nm, tmp], hC)]

/-- **A crash of the claims after the minting is one of the claims before it** (the minting adds
the name `tmp`, and splits `nm` off the area claim into the creating claim). The area claim's history
is its own restriction (`namesOf`'s: every entry writes one of its names). -/
theorem regionCrashedK_mint {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH}
    {nm tmp : GoString} {hC : NamesH} (hc : (jr, N, h) ∈ cl) (hself : h.restrict jr N = h)
    (hnm : N.Mem nm) (hCr : hC.restrict jr (N.inter [nm]) = h.restrict jr (N.inter [nm]))
    {n : Nat} {m' : Tree} {K : Nat → Prop}
    (hK : RegionCrashedK (mintClaims cl jr N h nm tmp hC) n m' K) : RegionCrashedK cl n m' K := by
  classical
  have hinI : (N.inter [nm]).Mem nm := (N.mem_inter [nm] nm).2 ⟨hnm, List.mem_singleton_self _⟩
  have hR : (jr, N.diff [nm], h.restrict jr (N.diff [nm])) ∈ mintClaims cl jr N h nm tmp hC := by
    have := mem_replClaim (c0 := (jr, N, h)) (c1 := (jr, N.diff [nm], h.restrict jr (N.diff [nm]))) hc
    rw [if_pos rfl] at this
    exact List.mem_append_left _ this
  have hCm : (jr, NameSet.only [nm, tmp], hC) ∈ mintClaims cl jr N h nm tmp hC :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hO : ∀ c ∈ cl, c ≠ (jr, N, h) → c ∈ mintClaims cl jr N h nm tmp hC := fun c hc' hne => by
    have := mem_replClaim (c0 := (jr, N, h)) (c1 := (jr, N.diff [nm], h.restrict jr (N.diff [nm]))) hc'
    rw [if_neg hne] at this
    exact List.mem_append_left _ this
  refine regionCrashedK_cover (fun c hc' x e E hx => ?_) (fun c hc' b hb => ?_) hK
  · by_cases hce : c = (jr, N, h)
    · subst hce
      simp only at hx
      rw [← hself] at hx
      obtain ⟨b, hbN, hw⟩ := restrict_ents_writes hx
      rw [hself] at hx
      by_cases hbn : b = nm
      · subst hbn
        have h1 := mem_restrict_ents hx hinI hw
        rw [← hCr] at h1
        obtain ⟨E', hE'⟩ := restrict_ents_mem h1
        exact ⟨_, hCm, E', hE'⟩
      · have hbD : (N.diff [nm]).Mem b := (N.mem_diff [nm] b).2 ⟨hbN, by simpa using hbn⟩
        exact ⟨_, hR, _, mem_restrict_ents hx hbD hw⟩
    · exact ⟨c, hO c hc' hce, E, hx⟩
  · by_cases hce : c = (jr, N, h)
    · subst hce
      simp only at hb ⊢
      by_cases hbn : b = nm
      · subst hbn
        refine ⟨_, hCm, rfl, by simp [NameSet.Mem], fun K' => ?_⟩
        simp only
        rw [← valAfter_restrict hC jr _ K' _ hinI, hCr, valAfter_restrict h jr _ K' _ hinI]
      · have hbD : (N.diff [nm]).Mem b := (N.mem_diff [nm] b).2 ⟨hb, by simpa using hbn⟩
        exact ⟨_, hR, rfl, hbD, fun K' => valAfter_restrict h jr _ K' b hbD⟩
    · exact ⟨c, hO c hc' hce, rfl, hb, fun _ => rfl⟩

/-! ## Dropping a claim -/

/-- The claims' entries are the log's (as the shared invariant's `NamesCoh` has them: every claim's
history is `namesOf` of the history). -/
def ClaimsLog (log : List LogEntry) (cl : List Claim) : Prop :=
  ∀ c ∈ cl, ∀ x e E, (x, e, E) ∈ c.2.2.ents → log[x]? = some e

/-- `y` is the index of an entry of one of the claims `cl`. -/
def InIdx (cl : List Claim) (y : Nat) : Prop := ∃ c ∈ cl, ∃ e E, (y, e, E) ∈ c.2.2.ents

/-- **The kept set extended to a dropped claim's entries**: `K` on the remaining claims' entries;
another entry is kept if below `n`, or if it took effect before a kept remaining entry's call began. -/
def dropK (cl : List Claim) (n : Nat) (K : Nat → Prop) (y : Nat) : Prop :=
  (InIdx cl y ∧ K y) ∨
    (¬ InIdx cl y ∧ (y < n ∨ ∃ c ∈ cl, ∃ x e E, (x, e, E) ∈ c.2.2.ents ∧ K x ∧ y < e.start))

theorem dropK_of {cl : List Claim} {n : Nat} {m' : Tree} {K : Nat → Prop} {y : Nat}
    (hK : RegionCrashedK cl n m' K)
    (h : y < n ∨ ∃ c ∈ cl, ∃ x e E, (x, e, E) ∈ c.2.2.ents ∧ K x ∧ y < e.start) :
    dropK cl n K y := by
  by_cases hy : InIdx cl y
  · refine Or.inl ⟨hy, ?_⟩
    obtain ⟨c', hc', e', E', hy'⟩ := hy
    rcases h with h | ⟨c, hc, x, e, E, hx, hKx, hlt⟩
    · exact hK.2.1 c' hc' y e' E' hy' h
    · exact hK.1 c hc c' hc' x e E y e' E' hx hy' hKx hlt
  · exact Or.inr ⟨hy, h⟩

theorem dropK_iff {cl : List Claim} {n : Nat} {K : Nat → Prop} {y : Nat} (hy : InIdx cl y) :
    dropK cl n K y ↔ K y :=
  ⟨fun h => h.elim (·.2) (fun h' => absurd hy h'.1), fun h => Or.inl ⟨hy, h⟩⟩

/-- **Dropping a one-name claim** (`b` of `j`, no remaining claim's): a crash of the remaining
claims is, with `b` reset to what the dropped claim says after the extended kept set, a crash of
all of them; the remaining claims' kept entries unchanged. Needs the claims' entries to be one log's,
which `Starts` (an entry's call began no later than it took effect). -/
theorem regionCrashedK_drop1 {log : List LogEntry} (hst : Starts log) {cl : List Claim} {j : Ino}
    {b : GoString} {h : NamesH} (hlog : ClaimsLog log ((j, .only [b], h) :: cl))
    (hdisj : ∀ c ∈ cl, c.1 = j → ¬ c.2.1.Mem b)
    {n : Nat} {m' : Tree} {K : Nat → Prop} (hK : RegionCrashedK cl n m' K) :
    RegionCrashedK ((j, .only [b], h) :: cl) n (treeSetE m' j b (h.valAfter j (dropK cl n K) b))
      (dropK cl n K) := by
  refine ⟨?_, fun c1 _ y e E _ hlt => dropK_of hK (Or.inl hlt), ?_⟩
  · intro c1 hc1 c2 _ x e E y e' E' hx _ hKx hlt
    apply dropK_of hK
    have hxl := hlog c1 hc1 x e E hx
    have hs := hst x e hxl
    rcases hKx with ⟨⟨c0, hc0, e0, E0, hx0⟩, hK0⟩ | ⟨-, hxn | ⟨c3, hc3, x3, e3, E3, hx3, hK3, hlt3⟩⟩
    · have h0 := hlog c0 (List.mem_cons_of_mem _ hc0) x e0 E0 hx0
      rw [hxl] at h0
      cases h0
      exact Or.inr ⟨c0, hc0, x, e, E0, hx0, hK0, hlt⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨c3, hc3, x3, e3, E3, hx3, hK3, by omega⟩
  · intro c1 hc1 b' hb'
    rcases List.mem_cons.1 hc1 with rfl | hc1
    · simp only [NameSet.Mem, List.mem_singleton] at hb'
      subst hb'
      rw [treeSetE_entry]
      simp
    · rw [treeSetE_entry, if_neg (fun (hjb : c1.1 = j ∧ b' = b) => hdisj c1 hc1 hjb.1 (hjb.2 ▸ hb')),
        hK.2.2 c1 hc1 b' hb']
      exact valAfter_congrK _ _ _ _ _ (fun (xe : Nat × LogEntry × Ents) hxe =>
        (dropK_iff ⟨c1, hc1, xe.2.1, xe.2.2, hxe⟩).symm)

end pure

end WalFs
end EtcdGrove
end Perennial

end
