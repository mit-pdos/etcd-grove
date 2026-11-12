/- Lean-first (no Rocq counterpart).

`workloadNodes()` (k8s_etcd3.go): the workload's nodes, `""`, `node-1`, `node-2` (`""` for none).
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

/-- The workload's nodes. -/
abbrev wndD : List GoString := [go!"", go!"node-1", go!"node-2"]

/-- See the file header. -/
abbrev workloadNodes.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadNodes)) (Val #()))
  {{ (out : GoSlice), RET #out; out ↦* wndD ∗ ownSliceCap GoString out (DFrac.own 1) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
