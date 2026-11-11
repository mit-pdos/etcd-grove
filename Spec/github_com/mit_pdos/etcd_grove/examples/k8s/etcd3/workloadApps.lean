/- Lean-first (no Rocq counterpart).

`workloadApps()` (k8s_etcd3.go): the workload's apps (labels), `""`, `app-a`, `app-b` (`""` for none).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- The workload's apps (labels). -/
abbrev wapD : List GoString := [go!"", go!"app-a", go!"app-b"]

/-- See the file header. -/
abbrev workloadApps.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadApps)) (Val #()))
  {{ (out : GoSlice), RET #out; out ↦* wapD ∗ ownSliceCap GoString out (DFrac.own 1) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
