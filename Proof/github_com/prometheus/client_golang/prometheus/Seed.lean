/-
The trusted `init()` of prometheus (`TrustedCode/github_com/prometheus/client_golang/prometheus.lean`,
route (b), notes/prom-registry.md): what its inserts do, and the names of the types it writes literally
(the trusted file cannot name the translation's, which imports it).
-/
module

public import GeneratedProof.github_com.prometheus.client_golang.prometheus
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus

open Iris Iris.BI Iris.ProofMode
open github_com.prometheus.client_golang.prometheus

/-- The trusted file's `Registry` is the translation's. -/
theorem seed_Registry_eq [GooseExts] [GoGlobalContext] : seed.Registry = Registry.ty := by
  with_unfolding_all rfl

/-- The trusted file's `Collector` is the translation's. -/
theorem seed_Collector_eq [GooseExts] [GoGlobalContext] : seed.Collector = Collector.ty := by
  with_unfolding_all rfl

/-- The trusted file's name of the variable `defaultRegistry` is the translation's. -/
theorem seed_defaultRegistry_eq [GooseExts] [GoGlobalContext] :
    go!"github.com/prometheus/client_golang/prometheus.defaultRegistry" = defaultRegistry := rfl

/-- The inserts of a list of pairs, in order, into a map. -/
def insertList {K V : Type} [DecidableEq K] (ps : List (K × V)) (M : GMap K V) : GMap K V :=
  ps.foldl (fun M p => <[p.1 := p.2]> M) M

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `seed.insertAll kt vs m` inserts the pairs `xs.map f` (`vs`, as values) into the map `m`, in order. -/
theorem wp_seed_insertAll {K V α : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V]
    [go.IntoValInj K] (kt : go.GoType) [Hsafe : ∀ k : K, SafeMapKey (GF := GF) kt k] (f : α → K × V) :
    ∀ (xs : List α) (m : Loc) (M : GMap K V),
    {{ (m ↦$ M : IProp GF) }}
      (App (Val (seed.insertAll kt (xs.map fun x => (#(f x).1, #(f x).2)))) (Val #m))
    {{ RET #(); m ↦$ insertList (xs.map f) M }}
  | [], m, M => by
    wp_start as Hm
    try simp only [List.map_nil, seed.insertAll]
    rw [show insertList ([] : List (K × V)) M = M from rfl]
    iapply HΦ $$ Hm
  | x :: xs, m, M => by
    wp_start as Hm
    try simp only [List.map_cons, seed.insertAll]
    wp_apply (wp_mapInsert (K := K) (V := V) kt m M (f x).1 (f x).2) $$ Hm as Hm
    wp_apply (wp_seed_insertAll kt f xs m (<[(f x).1 := (f x).2]> M)) $$ Hm as Hm
    rw [show insertList (f x :: xs.map f) M = insertList (xs.map f) (<[(f x).1 := (f x).2]> M) from rfl]
    iapply HΦ $$ Hm

end proof

end prometheus
end EtcdGrove
end Perennial
