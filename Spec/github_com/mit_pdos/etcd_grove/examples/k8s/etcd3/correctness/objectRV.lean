/-
Lean-first (no Rocq counterpart).

`objectRV(obj, versioner)` (`correctness/watch.go`) of a driver's `*Obj` (read-only, `deepRO`), with
the driver's versioner: its resource version and `nil` (`meta.Accessor` returns the object, its
`GetResourceVersion` is the versioner's string form of the field, which parses back) (k8s 7g step 5).
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
abbrev objectRV.spec : Prop :=
  ∀ (x : GoInterface) (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ deepRO x (.obj o) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.objectRV))
      (Val #x)) (Val #(versionerV)))
  {{ RET (PairV #o.ResourceVersion' #GoInterface.nil); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
