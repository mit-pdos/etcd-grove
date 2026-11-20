/-
Lean-first (no Rocq counterpart).

`validateMaybeLastEventError(events)` (`correctness/watch.go`) of read-only events of views `rs` the
pure check accepts (`lastErrOkL rs`: every Error event holds a `*metav1.Status` of status `Failure`
and is the last one): `nil` (k8s 7g step 5; accepting runs only).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.EvRep

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
abbrev validateMaybeLastEventError.spec : Prop :=
  ∀ (sl : GoSlice) (rs : List REv),
  lastErrOkL rs = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      evsRO sl rs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.validateMaybeLastEventError))
      (Val #sl))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
