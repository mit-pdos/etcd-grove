/- Lean-first (no Rocq counterpart).

# `Discard`'s step S, pure: dropping a WAL directory's claim (P6b state C, mit-pdos/etcd-grove#50;
`notes/wal-p6-handoff.md`, session 18)

At S (the area's fsync after `Discard`'s rename) the discarded WAL's directory claim `(J, N, h)` leaves the
invariant's claims `cl` (the program takes it whole, tagged `tmpName nm`, into `walAreaRes`). Fewer claims
allow more crashed trees; as `regionCrashedK_drop1` (`CreateDrop.lean`) for a one-name claim, a crash `m'`
of the remaining claims is, with `J`'s names of `N` set to what the dropped claim says after the extended
kept set (`dropK`), a crash of all of them (`regionCrashedK_dropDir`), the tree unchanged elsewhere. The
directory's entries are a finite map: `exists_dir` (every name the dropped claim or `m'` gives a value is in
a list of candidates).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDrop

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

theorem lookup_ofList_filterMap (f : GoString → Option Node) (L : List GoString) (b : GoString) :
    (GMap.ofList (L.filterMap (fun c => (f c).map (c, ·)))) !! b = if b ∈ L then f b else none := by
  induction L with
  | nil => simp only [GMap.ofList, List.filterMap_nil]; exact GMap.lookup_empty b
  | cons c L ih =>
    simp only [List.filterMap_cons]
    cases hc : f c with
    | none =>
      simp only [Option.map_none]
      rw [ih]
      by_cases hb : b ∈ L
      · simp [hb]
      · by_cases e : b = c
        · subst e; simp [hb, hc]
        · simp [hb, e]
    | some v =>
      simp only [Option.map_some, GMap.ofList]
      by_cases e : c = b
      · subst e; rw [GMap.lookup_insert_eq]; simp [hc]
      · rw [GMap.lookup_insert_ne _ _ e, ih]
        have e' : b ≠ c := fun h => e h.symm
        by_cases hb : b ∈ L <;> simp [hb, e']

/-- **A directory with given entries** (a function supported on a list of candidates). -/
theorem exists_dir (f : GoString → Option Node) (L : List GoString) (hL : ∀ b, f b ≠ none → b ∈ L) :
    ∃ D : Dir, ∀ b, D !! b = f b := by
  refine ⟨GMap.ofList (L.filterMap (fun c => (f c).map (c, ·))), fun b => ?_⟩
  rw [lookup_ofList_filterMap]
  by_cases hb : b ∈ L
  · rw [if_pos hb]
  · rw [if_neg hb]
    cases hf : f b with
    | none => rfl
    | some v => exact absurd (hL b (by rw [hf]; simp)) hb

/-- The names a history gives a value to after any crash are among its entries' and its boot's. -/
theorem valAfter_cands (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString)
    (hb : h.valAfter j K b ≠ none) :
    b ∈ h.boot.toList.map (·.1) ++ h.ents.flatMap (fun xe => xe.2.2.toList.map (·.1)) := by
  classical
  unfold NamesH.valAfter at hb
  split at hb
  · rename_i xe hxe
    have hm : xe ∈ h.ents := (List.mem_filter.1 (List.mem_of_getLast? hxe)).1
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
    refine List.mem_append_right _ (List.mem_flatMap.2 ⟨xe, hm, ?_⟩)
    exact List.mem_map.2 ⟨(b, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
    exact List.mem_append_left _ (List.mem_map.2 ⟨(b, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩)

open Classical in
/-- **The tree `m` with the names `N` of the directory `j` set by `f`** (the rest as in `m`). -/
theorem exists_treeSetN (m : Tree) (j : Ino) (N : NameSet) (f : GoString → Option Node)
    (L : List GoString) (hL : ∀ b, N.Mem b → f b ≠ none → b ∈ L) :
    ∃ m'' : Tree, ∀ j' b, m''.entry j' b = if j' = j ∧ N.Mem b then f b else m.entry j' b := by
  classical
  let g : GoString → Option Node := fun b => if N.Mem b then f b else m.entry j b
  obtain ⟨D, hD⟩ := exists_dir g (L ++ ((m !! j).getD ∅).toList.map (·.1)) (fun b hb => by
    by_cases hN : N.Mem b
    · simp only [g, hN, ite_true] at hb
      exact List.mem_append_left _ (hL b hN hb)
    · simp only [g, hN, ite_false] at hb
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
      refine List.mem_append_right _ (List.mem_map.2 ⟨(b, v), (GMap.mem_toList _ _ _).2 ?_, rfl⟩)
      unfold Tree.entry at hv
      cases hmj : m !! j with
      | none => rw [hmj] at hv; cases hv
      | some D0 => rw [hmj] at hv; simpa using hv)
  refine ⟨m.upd j (fun _ => D), fun j' b => ?_⟩
  unfold Tree.upd Tree.entry
  by_cases e : j' = j
  · subst e
    rw [GMap.lookup_insert_eq]
    simp only [Option.bind_some, hD, g]
    by_cases hN : N.Mem b
    · simp [hN]
    · simp [hN, Tree.entry]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]
    simp [e]

open Classical in
/-- **Dropping a directory's claim** (`(j, N, h)`, no remaining claim on a name of `N` of `j`): a crash
of the remaining claims is, with `j`'s names of `N` reset to what the dropped claim says after the
extended kept set, a crash of all of them; the tree elsewhere unchanged. As `regionCrashedK_drop1`. -/
theorem regionCrashedK_dropDir {log : List LogEntry} (hst : Starts log) {cl : List Claim} {j : Ino}
    {N : NameSet} {h : NamesH} (hlog : ClaimsLog log ((j, N, h) :: cl))
    (hdisj : ∀ c ∈ cl, c.1 = j → ∀ b, N.Mem b → ¬ c.2.1.Mem b)
    {n : Nat} {m' : Tree} {K : Nat → Prop} (hK : RegionCrashedK cl n m' K) :
    ∃ m'' : Tree, RegionCrashedK ((j, N, h) :: cl) n m'' (dropK cl n K) ∧
      ∀ j' b, ¬ (j' = j ∧ N.Mem b) → m''.entry j' b = m'.entry j' b := by
  classical
  obtain ⟨m'', hm''⟩ := exists_treeSetN m' j N (h.valAfter j (dropK cl n K)) _
    (fun b _ hb => valAfter_cands h j _ b hb)
  refine ⟨m'', ⟨?_, fun c1 _ y e E _ hlt => dropK_of hK (Or.inl hlt), ?_⟩, fun j' b hn => ?_⟩
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
    · rw [hm'', if_pos ⟨rfl, hb'⟩]
    · rw [hm'']
      by_cases hjb : c1.1 = j ∧ N.Mem b'
      · exact absurd hb' (hdisj c1 hc1 hjb.1 b' hjb.2)
      · rw [if_neg hjb, hK.2.2 c1 hc1 b' hb']
        exact valAfter_congrK _ _ _ _ _ (fun (xe : Nat × LogEntry × Ents) hxe =>
          (dropK_iff ⟨c1, hc1, xe.2.1, xe.2.2, hxe⟩).symm)
  · rw [hm'', if_neg hn]

end pure

end WalFs
end EtcdGrove
end Perennial

end
