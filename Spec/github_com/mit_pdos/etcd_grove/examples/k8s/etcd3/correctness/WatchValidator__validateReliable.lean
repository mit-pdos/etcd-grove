/-
Lean-first (no Rocq counterpart).

`WatchValidator.validateReliable(request, events)` (`correctness/watch.go`) on the validator
`realCheck` builds over the frozen replay `R`, the driver's watch `x` as the request (`wreqRep`) and
read-only events of views `rs` the pure check accepts (`reliableOkR R x rs`): `nil` (k8s 7g step 5;
accepting runs only).
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
abbrev WatchValidator.validateReliable.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (x : Input)
    (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest)
    (sl : GoSlice) (rs : List REv),
  reliableOkR R x rs = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ wreqRep req x ∗ evsRO sl rs }}
    (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"validateReliable" #(validatorV rp))) (Val #req)) (Val #sl))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
