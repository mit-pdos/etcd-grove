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

theorem isSome_insert {V : Type} (M : GMap GoString V) (k' k : GoString) (v : V) :
    ((<[k' := v]> M) !! k).isSome = ((M !! k).isSome || decide (k' = k)) := by
  simp only [GMap.lookup_insert_eq_iff]; split <;> simp_all

theorem lookupKV_isSome_cons {α : Type} (k k' : GoString) (v : α) (l : List (GoString × α)) :
    (lookupKV k ((k', v) :: l)).isSome = (decide (k' = k) || (lookupKV k l).isSome) := by
  simp only [lookupKV]; split <;> simp_all

/-- The keys of a map literal's inserts are its entries' (both sides as disjunctions). -/
theorem lookupKV_isSome_nil {α : Type} (k : GoString) :
    (lookupKV k ([] : List (GoString × α))).isSome = false := rfl

theorem isSome_empty {V : Type} (k : GoString) : ((∅ : GMap GoString V) !! k).isSome = false := rfl

/-- A literal's inserts (in the entries' order) have the entries' keys: both sides the same
disjunction once reassociated. -/
macro "lit_keys" : tactic =>
  `(tactic| (intro k; (repeat rw [isSome_insert]); rw [isSome_empty]; simp only [lookupKV_isSome_cons, lookupKV_isSome_nil, Option.isSome_none, Bool.or_false, Bool.false_or, Bool.or_assoc, A, B, C]))

/-- A map value's entries (`kvsU (UVal.ofMap kvs)` reduces to `kvsOf kvs`). -/
def kvsU : UVal → List (GoString × UVal)
  | .map kvs => kvs
  | _ => []

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
