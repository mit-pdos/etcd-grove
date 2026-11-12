/- Lean-first (no Rocq counterpart).

`workloadKeys()` (`k8setcd3.go`): the workload's keys, `ns-1/pod-1`, `ns-1/pod-11`, `ns-2/pod-2`,
`ns-11/pod-1` (stage 7e-0: namespaced, with a name prefix and a namespace prefix of another key).
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

/-- The workload's keys. -/
abbrev wksD : List GoString := [go!"ns-1/pod-1", go!"ns-1/pod-11", go!"ns-2/pod-2", go!"ns-11/pod-1"]

/-- See the file header. -/
abbrev workloadKeys.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadKeys)) (Val #()))
  {{ (out : GoSlice), RET #out; out ↦* wksD ∗ ownSliceCap GoString out (DFrac.own 1) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
