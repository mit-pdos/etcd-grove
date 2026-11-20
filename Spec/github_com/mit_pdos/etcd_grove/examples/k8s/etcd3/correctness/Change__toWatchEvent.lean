/-
Lean-first (no Rocq counterpart).

`Change.toWatchEvent(versioner, pred)` (`correctness/watch.go`) of a replay's change of view `c` (with
an object or the one before it, `chgOk c`: the panic is unreachable), with the driver's versioner and
the predicate of the driver's watch `x` (`watchOptions(in)`'s, `predWV x x.Bookmarks'`): no error, and
`nil` when `toWatchEventL x c` is none, else a fresh `*watch.Event` holding an event of its view
(k8s 7g step 5). The driver's package is initialized (its objects' methods).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Change.toWatchEvent.spec : Prop :=
  ∀ (cv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change) (c : RChange)
    (x : Input),
  chgOk c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ changeVRep cv c }}
    (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change.ty
      go!"toWatchEvent" #cv)) (Val #(versionerV))) (Val #(k8s_etcd3.predWV x x.Bookmarks')))
  {{ (ep : Loc) (err : GoInterface), RET (PairV #ep #err);
      ⌜err = GoInterface.nil⌝ ∗
      match toWatchEventL x c with
      | none => ⌜ep = null⌝
      | some r => ∃ v, ep ↦ v ∗ evRep v r }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
