/-
Lean-first (no Rocq counterpart).

`WatchValidator.toEventReference(events)` (`correctness/watch.go`) on the validator `realCheck` builds
(`validatorV rp`: the driver's `keyFunc`, the replay's versioner) and read-only events of views `rs`
that all have references (`rs.mapM evRefL = some refs`: each holds a driver's `*Obj`): no error and a
fresh, non-`nil` slice of the references (`erefV`) (k8s 7g step 5).
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
abbrev WatchValidator.toEventReference.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (sl : GoSlice) (rs : List REv) (refs : List (GoString × GoString × w64)),
  rs.mapM evRefL = some refs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ evsRO sl rs }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"toEventReference" #(validatorV rp))) (Val #sl))
  {{ (rsl : GoSlice) (err : GoInterface), RET (PairV #rsl #err);
      ⌜err = GoInterface.nil ∧ rsl ≠ slice.nil⌝ ∗ rsl ↦* refs.map erefV }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
