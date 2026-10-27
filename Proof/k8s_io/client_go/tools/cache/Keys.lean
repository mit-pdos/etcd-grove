/-
The store keys of client-go's `tools/cache` (`store.go`, `object-names.go`), as pure functions.
Lean-first; phase 2 of the DaemonSet plan (`notes/k8s-daemonset-plan.md`).

`nameKey ns name` is `ObjectName{ns, name}.String()` (and `MetaNamespaceKeyFunc`'s key of an object
with that namespace and name): `ns/name`, or `name` for an empty namespace. `splitKey key` is what
`SplitMetaNamespaceKey(key)` returns: the parts of `key` around `/` if there are one or two, else an
error (`none`). `splitKey_nameKey`: for a namespace and a name without `/` (which Kubernetes'
validation guarantees), splitting a key gives back its parts.
-/
module

public import GeneratedProof.k8s_io.client_go.tools.cache
public import Proof.k8s_io.client_go.tools.cache.Init
public import Perennial.Proof.strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

/-- `ObjectName{ns, name}.String()`. -/
def nameKey (ns name : GoString) : GoString := if ns = [] then name else ns ++ go!"/" ++ name

/-- `SplitMetaNamespaceKey(key)`'s result: the namespace and name, or `none` for an error. -/
def splitKey (key : GoString) : Option (GoString × GoString) :=
  match strings.split key go!"/" with
  | [n] => some ([], n)
  | [ns, n] => some (ns, n)
  | _ => none

/-- No `/` in a string. -/
def noSlash (s : GoString) : Prop := ∀ c ∈ s, c ≠ (47 : w8)

theorem splitAux_noSlash (r field : GoString) (h : noSlash r) :
    strings.splitAux go!"/" r field = [field ++ r] := by
  induction r generalizing field with
  | nil => simp [strings.splitAux]
  | cons c r ih =>
    have hc : c ≠ (47 : w8) := h c (List.mem_cons_self)
    have hr : noSlash r := fun d hd => h d (List.mem_cons_of_mem _ hd)
    rw [strings.splitAux]
    have : ¬ (go!"/" ≠ [] ∧ go!"/" <+: c :: r) := by
      rintro ⟨-, t, ht⟩
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
      exact hc ht.1.symm
    rw [if_neg this, ih _ hr]
    simp

/-- A key with a `/` between two parts without one splits into them. -/
theorem splitAux_slash (a b : GoString) (ha : noSlash a) (hb : noSlash b) :
    strings.splitAux go!"/" (a ++ go!"/" ++ b) [] = [a, b] := by
  suffices h : ∀ field, strings.splitAux go!"/" (a ++ go!"/" ++ b) field = [field ++ a, b] by
    simpa using h []
  induction a with
  | nil =>
    intro field
    simp only [List.nil_append, List.cons_append]
    rw [strings.splitAux, if_pos ⟨by simp, ⟨b, rfl⟩⟩]
    simp only [List.cons.injEq, List.append_nil, true_and]
    simpa using splitAux_noSlash b [] hb
  | cons c a ih =>
    intro field
    have hc : c ≠ (47 : w8) := ha c (List.mem_cons_self)
    have ha' : noSlash a := fun d hd => ha d (List.mem_cons_of_mem _ hd)
    simp only [List.cons_append]
    rw [strings.splitAux]
    have : ¬ (go!"/" ≠ [] ∧ go!"/" <+: c :: (a ++ go!"/" ++ b)) := by
      rintro ⟨-, t, ht⟩
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
      exact hc ht.1.symm
    rw [if_neg this]
    have := ih ha' (field ++ [c])
    simp only [List.append_assoc] at this ⊢
    rw [this]
    simp

/-- **Splitting a key gives back its parts** (a namespace and name without `/`). -/
theorem splitKey_nameKey (ns name : GoString) (hns : noSlash ns) (hname : noSlash name) :
    splitKey (nameKey ns name) = some (ns, name) := by
  unfold splitKey nameKey strings.split
  by_cases h : ns = []
  · subst h
    simp only [↓reduceIte]
    rw [splitAux_noSlash name [] hname]
    simp
  · simp only [h, ↓reduceIte]
    rw [splitAux_slash ns name hns hname]

end cache
end EtcdGrove
end Perennial
