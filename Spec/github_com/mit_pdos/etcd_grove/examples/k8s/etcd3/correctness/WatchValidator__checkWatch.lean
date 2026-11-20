/-
Lean-first (no Rocq counterpart).

`WatchValidator.checkWatch(request)` (`correctness/watch.go`) on the validator `realCheck` builds and
the driver's watch `x` as the request (`wreqRep`), a watch `checkWatch` accepts (`wInPre x`): `nil`,
and none of its panics (k8s 7g step 5). The driver's package is initialized (its versioner and
selectors).
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
abbrev WatchValidator.checkWatch.spec : Prop :=
  ∀ (rp : Loc) (x : Input)
    (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest),
  wInPre x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ wreqRep req x }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"checkWatch" #(validatorV rp))) (Val #req))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
