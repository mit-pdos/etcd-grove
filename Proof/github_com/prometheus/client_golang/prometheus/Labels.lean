/-
A prometheus metric vector's label names (D19l (iii), 2026-10-18): what `WithLabelValues` and
`With` check before they return a metric (client_golang v1.24.1, the version etcd's
`server/go.mod` pins). `(*MetricVec).GetMetricWithLabelValues` (`vec.go`) returns an error, which
`CounterVec`/`GaugeVec`/`HistogramVec.WithLabelValues` turn into a panic (`counter.go:283`,
`gauge.go:237`, `histogram.go:1263`; `With`, `gauge.go:249`), unless there are as many values as the vector has variable
labels and each is valid UTF-8 (`validateLabelValues`, `labels.go:166`); `GetMetricWith` (`With`)
unless the map has as many entries as there are labels, one for each label name, each value valid
UTF-8 (`validateValuesInLabels`, `hashLabels`). (No vector here is curried or has label
constraints: `curry` is empty, `constrain` the identity.)

`vecLabels v ls` (opaque, pure, so persistent): `v` is a `*CounterVec`/`*GaugeVec`/`*HistogramVec`
built by `prometheus.New<Kind>Vec(opts, ls)`, uncurried, with unconstrained, pairwise distinct
valid variable labels `ls` and a valid name (`labelNamesOk`, `nameOk`); a `*HistogramVec` also
with buckets `NewHistogram` accepts and no label `le` (what its lazily built histograms check:
`newHistogram`). Only the constructors' trust-boundary specs state it (`NewCounterVec`,
`NewGaugeVec`, `NewHistogramVec`, metric-vecs 2026-11-19; until then the trust-boundary axioms
`<X>_init` of the vectors' untranslated initializers, `etc/gen-init.py`).
-/
module

public import GeneratedProof.github_com.prometheus.client_golang.prometheus
public import Proof.unicode.utf8.Valid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus

/-- The metric vector `v` has the variable labels `ls` (pairwise distinct; uncurried,
unconstrained). Opaque: only the vectors' constructors' trust-boundary specs state it. -/
opaque vecLabels (v : Loc) (ls : List GoString) : Prop

/-- A label name `NewDesc` accepts (`checkLabelName`: `model.UTF8Validation.IsValidLabelName`,
non-empty valid UTF-8, and no reserved prefix `__`), stated for ASCII names (valid UTF-8).
Decidable: `decide` checks a literal. -/
def labelNameOk (l : GoString) : Prop :=
  l ≠ [] ∧ (∀ b ∈ l, b.toNat < 128) ∧ l.take 2 ≠ [W8 95, W8 95]

instance (l : GoString) : Decidable (labelNameOk l) := by unfold labelNameOk; infer_instance

/-- Variable label names a vector's `NewDesc` accepts (no error recorded in its descriptor): each
valid (`labelNameOk`), pairwise distinct ("duplicate label names"). Decidable. -/
def labelNamesOk (ls : List GoString) : Prop :=
  ls.Nodup ∧ ∀ l ∈ ls, labelNameOk l

instance (ls : List GoString) : Decidable (labelNamesOk ls) := by unfold labelNamesOk; infer_instance

/-- Label values `WithLabelValues` accepts for the label names `ls`: one per label, each valid
UTF-8 (`validateLabelValues`). -/
def labelValuesOk (ls vs : List GoString) : Prop :=
  vs.length = ls.length ∧ ∀ v ∈ vs, utf8Valid v

/-- A label map `With` accepts for the label names `ls` (distinct): its keys exactly `ls`, its
values valid UTF-8 (`validateValuesInLabels` and `hashLabels`). -/
def labelMapOk (ls : List GoString) (M : GMap GoString GoString) : Prop :=
  ls.Nodup ∧ (∀ k, k ∈ ls ↔ ∃ v, M !! k = some v) ∧ ∀ k v, M !! k = some v → utf8Valid v

/-- Two values, the first a literal checked by `decide`. -/
theorem labelValuesOk_two (a b l1 l2 : GoString) (ha : utf8Valid a) (hb : utf8Valid b) :
    labelValuesOk [l1, l2] [a, b] := by
  refine ⟨rfl, ?_⟩
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact ha
  · exact hb

/-- A one-entry map for a one-label vector. -/
theorem labelMapOk_one (l v : GoString) (hv : utf8Valid v) :
    labelMapOk [l] (<[l := v]> (∅ : GMap GoString GoString)) := by
  refine ⟨List.Pairwise.cons (by simp) List.Pairwise.nil, ?_, ?_⟩
  · intro k
    by_cases hk : k = l
    · subst hk; simp
    · have : ¬ l = k := fun h => hk h.symm
      simp [hk, this]
  · intro k w hw
    by_cases hk : k = l
    · subst hk; simp at hw; subst hw; exact hv
    · have : ¬ l = k := fun h => hk h.symm
      simp [this] at hw

end prometheus
end EtcdGrove
end Perennial
