/-
The driver's literals and steps, the pure facts `Main`'s proof uses: a managers premise from the
decided ones of `Steps.lean`, and a one-conflict list from its set. Lean-first (2026-11-19).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Steps
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open smd

theorem lookupKV_mem {α : Type} (k : GoString) (l : List (GoString × α)) (v : α)
    (h : lookupKV k l = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [lookupKV] at h
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [lookupKV] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rename_i hk; subst hk; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- `Apply`'s managers premise from the decided `version_all`/`kwi_all` facts. -/
theorem mf_premise (hkwi : keysWithItemsB_iff.law) (mf : MF)
    (hv : ∀ me ∈ mf, me.2.version = version)
    (hk : ∀ me ∈ mf, keysWithItemsB sc0 rootRef me.2.set = true) :
    ∀ m e, mf.get m = some e → e.version = version ∧ keysWithItems sc0 rootRef e.set := by
  intro m e h
  have hm := lookupKV_mem m mf e h
  exact ⟨hv _ hm, (hkwi _ _ _).1 (hk _ hm)⟩

/-- A duplicate-free list with the members of a singleton set is that singleton. -/
theorem nodup_ofList_singleton {α : Type} (l : List α) (x : α) (hnd : l.Nodup)
    (h : FSet.ofList l = FSet.ofList [x]) : l = [x] := by
  have hs : ∀ y, y ∈ l ↔ y ∈ [x] := Quotient.exact h
  match l, hnd with
  | [], _ => simpa using (hs x)
  | a :: t, hnd =>
    have ha : a = x := by simpa using (hs a).1 (by simp)
    subst ha
    cases t with
    | nil => rfl
    | cons b t' =>
      have hb : b = a := by simpa using (hs b).1 (by simp)
      subst hb
      simp at hnd

end k8s_smd
end EtcdGrove
end Perennial
