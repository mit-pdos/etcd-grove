/-
Lean-first (no Rocq counterpart).

`WatchValidator.validateInitialEvents(request, initialEvents, bookmarkRV)` (`correctness/watch.go`) on
the validator `realCheck` builds over the frozen replay `R`, the driver's watch `x` as the request
(`wreqRep`) and read-only events of views `init` the pure check accepts at the bookmark's resource
version `brv` (`initialOkL R x init brv`): `nil` (k8s 7g step 5; accepting runs only).
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
abbrev WatchValidator.validateInitialEvents.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (x : Input)
    (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest)
    (sl : GoSlice) (init : List REv) (brv : w64),
  initialOkL R x init brv = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ wreqRep req x ∗ evsRO sl init }}
    (App (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty
      go!"validateInitialEvents" #(validatorV rp))) (Val #req)) (Val #sl)) (Val #brv))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
