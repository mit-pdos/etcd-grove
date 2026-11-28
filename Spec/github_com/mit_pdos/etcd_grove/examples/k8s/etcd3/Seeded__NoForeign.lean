/-
Lean-first (no Rocq counterpart).

`Seeded.NoForeign(ops)` (`examples/k8s/etcd3/export.go`; k8s-dist K9 §2.8): when it returns true, the
history shows no foreign revision above the seeded store's (`s.st0.rv`): the revisions its successful
writes answer with above it are exactly the next ones up to some `m`, and no revision any operation
shows is above `m` (`NoForeignOk`). Its premises are `HistoryRevs`', which it calls: boxed `Input`s and
`Output`s meeting `HistOpOk`, and at most `2^62` revisions to record (`histCost`, the run-size bound
`RunSizeOk` of `notes/k8s-dist-k9.md`, a hypothesis until time receipts discharge it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.NoForeignDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Seeded)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Seeded.NoForeign.spec : Prop :=
  ∀ (s : Seeded) (sl : GoSlice) (ops : List github_com.anishathalye.porcupine.Operation)
    (xs : List (Input × Output)) (dq : DFrac),
  List.Forall₂ (fun o p => o.Input' = boxIn p.1 ∧ o.Output' = boxOut p.2) ops xs →
  (∀ p ∈ xs, HistOpOk p.1 p.2) →
  histCost xs ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      sl ↦*{dq} ops }}
    (App (Val #(methods Seeded.ty go!"NoForeign" #s)) (Val #sl))
  {{ (b : Bool), RET #b; sl ↦*{dq} ops ∗
      ⌜b = true → ∃ m : w64, NoForeignOk s.st0'.rv' xs m⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
