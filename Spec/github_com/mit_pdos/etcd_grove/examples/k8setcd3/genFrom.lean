/- Lean-first (no Rocq counterpart).

`genFrom(n)` (k8setcd3.go): an input `Gen` may return (`GenIn`: a workload key, one of the four kinds).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Calls

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
abbrev genFrom.spec : Prop :=
  ∀ (n : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.genFrom)) (Val #n))
  {{ (x : Input), RET #x; ⌜GenIn x⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
