/- Lean-first (no Rocq counterpart).

`pendEqual(a, b)` (export.go): whether the pending lists `a` and `b` hold the same inputs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3
  (mstore mcfg hnode Input histHashes cfgSet)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev pendEqual.spec : Prop :=
  ∀ (a b : GoSlice) (xs ys : List Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ a ↦*□ xs ∗ b ↦*□ ys }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pendEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (xs = ys)); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
