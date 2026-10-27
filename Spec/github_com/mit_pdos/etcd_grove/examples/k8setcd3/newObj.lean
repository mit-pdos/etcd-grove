/- Lean-first (no Rocq counterpart).

`newObj()` (k8setcd3.go): a new `*Obj`, as a `runtime.Object` (non-`nil`): the store's `newFunc`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev newObj.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.newObj)) (Val #()))
  {{ (x : GoInterface), RET #x; ⌜x ≠ GoInterface.nil⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
