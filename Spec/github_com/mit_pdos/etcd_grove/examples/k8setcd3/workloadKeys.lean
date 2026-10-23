/- Lean-first (no Rocq counterpart).

`workloadKeys()` (k8setcd3.go): the workload's keys, `a`, `b`, `c`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- The workload's keys. -/
abbrev wksD : List GoString := [go!"a", go!"b", go!"c"]

/-- See the file header. -/
abbrev workloadKeys.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.workloadKeys)) (Val #()))
  {{ (out : GoSlice), RET #out; out ↦* wksD ∗ ownSliceCap GoString out (DFrac.own 1) }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
