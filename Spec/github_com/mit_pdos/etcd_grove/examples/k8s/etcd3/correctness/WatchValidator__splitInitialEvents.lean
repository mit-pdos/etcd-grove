/-
Lean-first (no Rocq counterpart).

`WatchValidator.splitInitialEvents(events)` (`correctness/watch.go`) on the validator `realCheck`
builds and read-only events of views `rs` the pure split accepts (`splitInitL rs = some (a, b)`):
the events before the first bookmark (`a`) and the rest from it (`b`), both read-only, and no error
(k8s 7g step 5; accepting runs only). The driver's package is initialized (the annotation of its
objects).
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
abbrev WatchValidator.splitInitialEvents.spec : Prop :=
  ∀ (rp : Loc) (sl : GoSlice) (rs a b : List REv),
  splitInitL rs = some (a, b) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ evsRO sl rs }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"splitInitialEvents" #(validatorV rp))) (Val #sl))
  {{ (s1 s2 : GoSlice) (err : GoInterface), RET (PairV (PairV #s1 #s2) #err);
      ⌜err = GoInterface.nil⌝ ∗ evsRO s1 a ∗ evsRO s2 b }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
