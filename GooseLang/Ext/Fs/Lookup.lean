/-
Facts about path resolution (`OsState.lookup`, `Impl.lean`): a canonical path splits uniquely into a
root and components. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- A list with no `/`, then either nothing or a `/` and more: the part before the first `/`. -/
theorem takeWhile_noslash {x y : GoString} (hx : slashB ∉ x) (hy : y = [] ∨ ∃ y', y = slashB :: y') :
    (x ++ y).takeWhile (· ≠ slashB) = x := by
  induction x with
  | nil =>
    rcases hy with rfl | ⟨y', rfl⟩ <;> simp
  | cons a x ih =>
    simp only [List.mem_cons, not_or] at hx
    have ha : decide (a ≠ slashB) = true := by simpa using Ne.symm hx.1
    rw [List.cons_append, List.takeWhile_cons, if_pos ha, ih hx.2]

theorem flatMap_slash_start (cs : List GoString) :
    cs.flatMap (slashB :: ·) = [] ∨ ∃ y', cs.flatMap (slashB :: ·) = slashB :: y' := by
  cases cs with
  | nil => left; rfl
  | cons c cs => right; exact ⟨c ++ cs.flatMap (slashB :: ·), by simp⟩

/-- Components with no `/`, each after a `/`, determine the components. -/
theorem flatMap_slash_inj : ∀ (cs ds : List GoString), (∀ c ∈ cs, slashB ∉ c) →
    (∀ d ∈ ds, slashB ∉ d) → cs.flatMap (slashB :: ·) = ds.flatMap (slashB :: ·) → cs = ds
  | [], [], _, _, _ => rfl
  | [], d :: ds, _, _, h => by simp at h
  | c :: cs, [], _, _, h => by simp at h
  | c :: cs, d :: ds, hc, hd, h => by
    simp only [List.flatMap_cons, List.cons_append, List.cons.injEq, true_and] at h
    have hcd : c = d := by
      have h1 := takeWhile_noslash (hc c (by simp)) (flatMap_slash_start cs)
      have h2 := takeWhile_noslash (hd d (by simp)) (flatMap_slash_start ds)
      rw [← h1, ← h2, h]
    subst hcd
    have := List.append_cancel_left h
    rw [flatMap_slash_inj cs ds (fun c h => hc c (by simp [h])) (fun d h => hd d (by simp [h])) this]

/-- The components of a path below one root determine the path's split. -/
theorem joinPath_inj {r : GoString} {cs ds : List GoString} (hc : ∀ c ∈ cs, NameOk c)
    (hd : ∀ d ∈ ds, NameOk d) (h : joinPath r cs = joinPath r ds) : cs = ds :=
  flatMap_slash_inj cs ds (fun c h => (hc c h).2.2.2.1) (fun d h => (hd d h).2.2.2.1)
    (List.append_cancel_left h)

/-- With one root, the path of components `cs` below it names what walking them names. -/
theorem lookup_one {st : OsState} {r : GoString} {j : Ino} (hr : st.fs.roots = [(r, j)])
    {cs : List GoString} (hcs : ∀ c ∈ cs, NameOk c) :
    st.lookup (joinPath r cs) = walk st.tree (.dir j) cs := by
  unfold OsState.lookup
  have hex : ∃ (rj : GoString × Ino) (cs' : List GoString), rj ∈ st.fs.roots ∧
      (∀ c ∈ cs', NameOk c) ∧ joinPath r cs = joinPath rj.1 cs' := ⟨(r, j), cs, by simp [hr], hcs, rfl⟩
  rw [dif_pos hex]
  have h1 := hex.choose_spec.choose_spec
  generalize hex.choose_spec.choose = cs0 at h1 ⊢
  generalize hex.choose = rj at h1 ⊢
  have hrj : rj = (r, j) := by simpa [hr] using h1.1
  subst hrj
  rw [(joinPath_inj hcs h1.2.1 h1.2.2).symm]

end Fs
end Perennial

end
