/-
Lean-first (no Rocq counterpart).

`watchRevisionRange(versioner, request, events)` (`correctness/watch.go`) with the driver's versioner,
the driver's watch `x` as the request (`wreqRep`) and read-only events of views `rs`, when the pure
function answers without error (`watchRangeL x rs = some o`): no error and the range `o`
(`rangeRep`) (k8s 7g step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchVocab

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
abbrev watchRevisionRange.spec : Prop :=
  ∀ (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest) (x : Input)
    (sl : GoSlice) (rs : List REv) (o : Option (w64 × w64)),
  watchRangeL x rs = some o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ wreqRep req x ∗ evsRO sl rs }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.watchRevisionRange))
      (Val #(versionerV))) (Val #req)) (Val #sl))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); ⌜err = GoInterface.nil⌝ ∗ rangeRep p o }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
