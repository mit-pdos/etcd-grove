/-
Lean-first (no Rocq counterpart).

# `toPorcupineModel`'s model on porcupine's values (k8s 7g step 5, decision 1)

Porcupine runs `correctness.Model`'s `Step` on boxed `Request`/`Response` values, whose views (`reqRep`,
`respRep`) need the heap. The model the spec of `toPorcupineModel` claims is `realS` lifted through a
decoder fixed once the operations are built: `decR L io`, the view of the first entry of `L` (each unary
operation's value with its view) whose value is `io`.

- `isLinearization_map`: a linearization carries over to a history of the same shape whose operations step
  alike (the same calls and returns; `M.step s o.val = M'.step s o'.val`; the same initial state);
- `decR L io`, `realM L init`: the decoder and the lifted model;
- `realM_step`: on an entry whose value's other entries step alike (`StepAgree`), the lifted model steps as
  `realS` on the entry's own view.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealLin

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section generic
variable {σ α β : Type}

theorem run_map (M : SeqModel σ α) (M' : SeqModel σ β) (h : List (Op α)) (h' : List (Op β))
    (hstep : ∀ (k : Nat) (o : Op α) (o' : Op β), h[k]? = some o → h'[k]? = some o' → ∀ s, M.step s o.val = M'.step s o'.val)
    (hlen : h.length = h'.length) :
    ∀ (π : List Nat) (s : σ), run M s (vals h π) = run M' s (vals h' π)
  | [], _ => rfl
  | k :: π, s => by
    cases ho : h[k]? with
    | none =>
      have ho' : h'[k]? = none := by
        rw [List.getElem?_eq_none_iff] at ho ⊢; omega
      simp only [vals, List.filterMap_cons, ho, ho', Option.map_none]
      exact run_map M M' h h' hstep hlen π s
    | some o =>
      obtain ⟨o', ho'⟩ : ∃ o', h'[k]? = some o' := by
        have : k < h'.length := hlen ▸ (List.getElem?_eq_some_iff.1 ho).1
        exact ⟨_, List.getElem?_eq_getElem this⟩
      simp only [vals, List.filterMap_cons, ho, ho', Option.map_some]
      simp only [run, hstep k o o' ho ho' s]
      cases M'.step s o'.val with
      | none => rfl
      | some t => exact run_map M M' h h' hstep hlen π t

/-- **A linearization carries over** to a history of the same shape whose operations step alike. -/
theorem isLinearization_map (M : SeqModel σ α) (M' : SeqModel σ β) (h : List (Op α)) (h' : List (Op β))
    (π : List Nat) (hlen : h.length = h'.length)
    (hop : ∀ (k : Nat) (o : Op α) (o' : Op β), h[k]? = some o → h'[k]? = some o' →
      o.call = o'.call ∧ o.ret = o'.ret ∧ ∀ s, M.step s o.val = M'.step s o'.val)
    (hinit : M.init = M'.init) (hπ : IsLinearization M h π) : IsLinearization M' h' π := by
  obtain ⟨hnd, hmem, hrun, hpw⟩ := hπ
  refine ⟨hnd, fun k => by rw [← hlen]; exact hmem k, ?_, ?_⟩
  · rw [← hinit, ← run_map M M' h h' (fun k o o' a b => (hop k o o' a b).2.2) hlen]; exact hrun
  · refine hpw.imp ?_
    intro a b hn hp
    apply hn
    obtain ⟨ob, oa, hb, ha, hlt⟩ := hp
    obtain ⟨ob0, hb0⟩ : ∃ o, h[b]? = some o := by
      have : b < h.length := hlen ▸ (List.getElem?_eq_some_iff.1 hb).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨oa0, ha0⟩ : ∃ o, h[a]? = some o := by
      have : a < h.length := hlen ▸ (List.getElem?_eq_some_iff.1 ha).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨-, hrb, -⟩ := hop b ob0 ob hb0 hb
    obtain ⟨hca, -, -⟩ := hop a oa0 oa ha0 ha
    exact ⟨ob0, oa0, hb0, ha0, by rw [hrb, hca]; exact hlt⟩

end generic

section go
variable [GooseExts]

open github_com.anishathalye.porcupine (OpV)

/-- **The decoder**: the view of the first entry of `L` whose value is `io`. -/
def decR (L : List (OpV × (Input × RResp))) (io : OpV) : Option (Input × RResp) :=
  (L.find? fun e => decide (e.1 = io)).map Prod.snd

/-- **`realS` lifted through the decoder.** -/
def realM (L : List (OpV × (Input × RResp))) (init : RM) : SeqModel RM OpV :=
  ⟨init, fun m io => match decR L io with
    | some v => (realS init).step m v
    | none => none⟩

/-- **The entries with one value step alike** under `realS`. -/
def StepAgree (L : List (OpV × (Input × RResp))) : Prop :=
  ∀ e ∈ L, ∀ e' ∈ L, e.1 = e'.1 → ∀ (init m : RM), (realS init).step m e.2 = (realS init).step m e'.2

theorem decR_mem (L : List (OpV × (Input × RResp))) (e : OpV × (Input × RResp)) (he : e ∈ L) :
    ∃ e' ∈ L, e'.1 = e.1 ∧ decR L e.1 = some e'.2 := by
  unfold decR
  obtain ⟨e', he'⟩ : ∃ e', L.find? (fun x => decide (x.1 = e.1)) = some e' := by
    cases hf : L.find? (fun x => decide (x.1 = e.1)) with
    | none =>
      exact absurd (List.find?_eq_none.1 hf e he) (by simp)
    | some e' => exact ⟨e', rfl⟩
  refine ⟨e', List.mem_of_find?_eq_some he', ?_, by rw [he']; rfl⟩
  simpa using List.find?_some he'

/-- **On an entry, the lifted model steps as `realS` on the entry's own view.** -/
theorem realM_step (L : List (OpV × (Input × RResp))) (init : RM) (hag : StepAgree L)
    (e : OpV × (Input × RResp)) (he : e ∈ L) (m : RM) :
    (realM L init).step m e.1 = (realS init).step m e.2 := by
  obtain ⟨e', he', h1, h2⟩ := decR_mem L e he
  show (match decR L e.1 with | some v => (realS init).step m v | none => none) = _
  rw [h2]
  exact hag e' he' e he h1 init m

end go

end k8s_correctness
end EtcdGrove
end Perennial
