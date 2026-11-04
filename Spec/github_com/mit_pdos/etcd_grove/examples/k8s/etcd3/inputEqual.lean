/- Lean-first (no Rocq counterpart).

`inputEqual(a, b)` (k8s_etcd3.go): `a = b` (Go's `==` on the struct).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev inputEqual.spec : Prop :=
  ∀ (a b : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.inputEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (a = b)); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
