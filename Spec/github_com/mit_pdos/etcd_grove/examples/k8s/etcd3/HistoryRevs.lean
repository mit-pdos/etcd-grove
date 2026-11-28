/- Lean-first (no Rocq counterpart).

`HistoryRevs(ops)` (export.go, notes/k8s-dist-k9.md §2.7): a `Revs` whose anchors are sorted, nonzero,
and (with 0) name every revision each operation shows (`AnchorsOk`), for operations whose inputs and
outputs are boxed `Input`s and `Output`s and meet `HistOpOk` (a precondition string shorter than
`rvOfMsg`'s pattern, a successful list's items that decode), and at most `2^62` revisions to record
(`histCost`: `slices.Sort` takes slices no longer than that). The keys' revisions (`byKey`,
`fastByKey`) are whatever Go computed: `settle` only adds configurations with them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HistRevsDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Revs)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev HistoryRevs.spec : Prop :=
  ∀ (sl : GoSlice) (ops : List github_com.anishathalye.porcupine.Operation)
    (xs : List (Input × Output)) (dq : DFrac),
  List.Forall₂ (fun o p => o.Input' = boxIn p.1 ∧ o.Output' = boxOut p.2) ops xs →
  (∀ p ∈ xs, HistOpOk p.1 p.2) →
  histCost xs ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      sl ↦*{dq} ops }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HistoryRevs)) (Val #sl))
  {{ (r : Revs), RET #r; sl ↦*{dq} ops ∗ ∃ R : RevsL, revsOwn r R ∗
      ⌜(∀ a ∈ R.anchors, a ≠ 0) ∧ k8s_dist.AnchorsOk (0 :: R.anchors.map uint.nat) xs⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
