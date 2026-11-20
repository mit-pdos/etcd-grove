/-
Lean-first (no Rocq counterpart).

`WatchValidator.compareEvents(expected, got)` (`correctness/watch.go`) on the validator `realCheck`
builds (`validatorV rp`) and read-only events of views `es` and `gs` the pure comparison accepts
(`compareEventsL es gs`: both have references, equal ones, and equal objects): `nil` (k8s 7g step 5;
accepting runs only: the rejection formats `cmp.Diff` of two objects, which has no spec).
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
abbrev WatchValidator.compareEvents.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (esl gsl : GoSlice) (es gs : List REv),
  compareEventsL es gs = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ evsRO esl es ∗ evsRO gsl gs }}
    (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"compareEvents" #(validatorV rp))) (Val #esl)) (Val #gsl))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
